#!/usr/bin/env python3
"""Turn `git log` output carrying `fixpt bench` tables into spreadsheet files.

    git log | scripts/bench-history.py                 # writes bench-history.{csv,xlsx}
    git log -20 main | scripts/bench-history.py -o out # writes out.csv and out.xlsx

Reads ordinary `git log` output (or any piece of it) on stdin. Each commit
is found by its `commit <hash>` line; with no such lines the whole input is
one commit. Within a commit every Markdown table whose header starts with
`| program` is read, and a table is named by its second column: `answer`
is the run table, `check` the compile table. The self-compile lines of the
migration commits (`new  0.08 s | 0.05 s | 1.81 s | 0.17 s |`) are read too,
as table `self` with programs `new` (best of the new lines) and `old`.
The run table's columns named before the machines were renamed (`lowered`,
`rust`, `hand`, …) are read under their names since (`RUN_RENAMED`).

Writes, oldest commit first:
  OUT.csv   long format: n, commit, date, subject, table, program, metric, value
  OUT.xlsx  one sheet per (table, metric), commits down, programs across,
            each with two charts over commit time (dates on the x axis, so
            gaps between commits show): the values, on a log scale when all
            are positive, and each program as a percentage of its first
            value, the y axis fitted to the data. Standard library only.
"""

import argparse
import csv
import re
import sys
import zipfile
from datetime import datetime
from xml.sax.saxutils import escape

SELF_PHASES = ["read", "parse", "check", "compile"]

# The run table's columns as named before 1567626 (TODO.md §78), each to
# its name since, so a machine's history is one series across the rename.
# The compile table's columns are phases, not machines, and were not
# renamed: its `registers` and `native` stay as they are.
RUN_RENAMED = {
    "lowered": "rs-scheme-vm",
    "rust": "rs-cells-rsinterp",
    "hand": "rs-cells-asminterp",
    "stencils": "rs-cells-stencils-cellcc",
    "compiled": "rs-cells-rsjit-cellcc",
    "registers": "rs-regs-rsjit-cellcc",
    "native": "rs-regs-rsjit-nativecc",
}


def split_commits(text):
    """Yield (hash, date, message lines) per commit, as `git log` printed them."""
    commits, cur = [], None
    for line in text.splitlines():
        m = re.match(r"^commit ([0-9a-f]{7,40})\b", line)
        if m:
            cur = {"hash": m.group(1), "date": "", "lines": []}
            commits.append(cur)
            continue
        if cur is None:
            cur = {"hash": "", "date": "", "lines": []}
            commits.append(cur)
        m = re.match(r"^(Date|AuthorDate|CommitDate):\s*(.*)$", line)
        if m and not cur["date"] and not cur["lines"]:
            cur["date"] = m.group(2).strip()
            continue
        if re.match(r"^(Author|Commit|Merge):", line) and not cur["lines"]:
            continue
        cur["lines"].append(line[4:] if line.startswith("    ") else line)
    return commits


def iso_date(d):
    """git's default date, or ISO already, as `YYYY-MM-DD HH:MM`."""
    for fmt in ("%a %b %d %H:%M:%S %Y %z", "%Y-%m-%dT%H:%M:%S%z", "%Y-%m-%d %H:%M:%S %z"):
        try:
            return datetime.strptime(d, fmt).strftime("%Y-%m-%d %H:%M")
        except ValueError:
            pass
    return d


def number(cell):
    cell = cell.strip()
    try:
        return float(cell)
    except ValueError:
        return None


def parse_commit(lines):
    """Return (subject, [(table, program, metric, value)])."""
    subject = next((l.strip() for l in lines if l.strip()), "")
    rows, header, table = [], None, None
    selfs = {"new": [], "old": []}
    for line in lines:
        s = line.strip()
        m = re.match(r"^(new|old)\s+((?:[\d.]+\s*s\s*\|\s*){4})$", s)
        if m:
            times = [float(t) for t in re.findall(r"([\d.]+)\s*s", m.group(2))]
            selfs[m.group(1)].append(times)
            continue
        if not s.startswith("|"):
            header = None
            continue
        cells = [c.strip() for c in s.strip("|").split("|")]
        if cells and cells[0] == "program":
            header = cells
            table = {"answer": "run", "check": "compile"}.get(cells[1], cells[1])
            if table == "run":
                header = [RUN_RENAMED.get(h, h) for h in header]
            continue
        if header is None or all(set(c) <= set("-: ") for c in cells):
            continue
        for metric, cell in zip(header[1:], cells[1:]):
            if metric == "answer":
                continue
            v = number(cell)
            if v is not None:
                rows.append((table, cells[0], metric, v))
    for who, runs in selfs.items():
        if runs:
            for i, phase in enumerate(SELF_PHASES):
                rows.append(("self", who, phase, min(r[i] for r in runs)))
    return subject, rows


def read_history(text):
    out = []
    for c in reversed(split_commits(text)):  # git log is newest first
        subject, rows = parse_commit(c["lines"])
        if rows:
            out.append({"hash": c["hash"][:10], "date": iso_date(c["date"]),
                        "subject": subject, "rows": rows})
    return out


def write_csv(path, history):
    with open(path, "w", newline="") as f:
        w = csv.writer(f)
        w.writerow(["n", "commit", "date", "subject", "table", "program",
                    "metric", "value"])
        for n, c in enumerate(history, 1):
            for table, program, metric, v in c["rows"]:
                w.writerow([n, c["hash"], c["date"], c["subject"], table,
                            program, metric, v])


# --- xlsx, written by hand -------------------------------------------------

def col(i):
    """0 -> A, 25 -> Z, 26 -> AA."""
    s = ""
    i += 1
    while i:
        i, r = divmod(i - 1, 26)
        s = chr(65 + r) + s
    return s


def sheet_name(table, metric, used):
    name = re.sub(r"[\[\]:*?/\\]", "_", f"{table} {metric}")[:31]
    base, k = name, 2
    while name in used:
        name = f"{base[:28]} {k}"
        k += 1
    used.add(name)
    return name


class Serial(float):
    """A date as a spreadsheet serial number (days since 1899-12-30)."""


def serial(iso):
    try:
        d = datetime.strptime(iso, "%Y-%m-%d %H:%M")
    except ValueError:
        return None
    return Serial((d - datetime(1899, 12, 30)).total_seconds() / 86400)


def date_range(dates):
    """The x axis's bounds: the dates' span, padded by 2% (at least an hour)."""
    xs = [float(d) for d in dates if isinstance(d, Serial)]
    if not xs:
        return None, None
    pad = max((max(xs) - min(xs)) * 0.02, 1 / 24)
    return min(xs) - pad, max(xs) + pad


def cell_xml(ref, v):
    if v is None:
        return ""
    if isinstance(v, Serial):
        return f'<c r="{ref}" s="1"><v>{float(v)!r}</v></c>'
    if isinstance(v, float):
        return f'<c r="{ref}"><v>{v!r}</v></c>'
    if isinstance(v, int):
        return f'<c r="{ref}"><v>{v}</v></c>'
    return f'<c r="{ref}" t="inlineStr"><is><t>{escape(v)}</t></is></c>'


def sheet_xml(grid, drawing):
    rows = []
    for r, values in enumerate(grid, 1):
        cells = "".join(cell_xml(f"{col(c)}{r}", v) for c, v in enumerate(values))
        rows.append(f'<row r="{r}">{cells}</row>')
    draw = '<drawing r:id="rId1"/>' if drawing else ""
    return ('<?xml version="1.0" encoding="UTF-8" standalone="yes"?>'
            '<worksheet xmlns="http://schemas.openxmlformats.org/spreadsheetml/2006/main" '
            'xmlns:r="http://schemas.openxmlformats.org/officeDocument/2006/relationships">'
            '<sheetViews><sheetView workbookViewId="0">'
            '<pane ySplit="1" topLeftCell="A2" activePane="bottomLeft" state="frozen"/>'
            '</sheetView></sheetViews>'
            '<cols><col min="1" max="1" width="5" customWidth="1"/>'
            '<col min="2" max="2" width="12" customWidth="1"/>'
            '<col min="3" max="3" width="17" customWidth="1"/>'
            '<col min="4" max="4" width="40" customWidth="1"/></cols>'
            f'<sheetData>{"".join(rows)}</sheetData>{draw}</worksheet>')


def y_range(values, pad=0.05):
    """Bounds that fit the values (not from 0), padded by `pad` of their span."""
    ys = [v for v in values if v is not None]
    if not ys:
        return None, None
    lo, hi = min(ys), max(ys)
    span = (hi - lo) or abs(hi) or 1
    return lo - span * pad, hi + span * pad


def chart_xml(title, sheet, programs, nrows, first_col, lo, hi, log=False, ylo=None, yhi=None):
    # A fortnight or less of history: label the axis with times too.
    fmt = "mm-dd hh:mm" if lo is not None and hi - lo <= 14 else "yyyy-mm-dd"
    q = "'" + sheet.replace("'", "''") + "'"
    series = []
    for i, p in enumerate(programs):
        c = col(first_col + i)
        series.append(
            f'<c:ser><c:idx val="{i}"/><c:order val="{i}"/>'
            f'<c:tx><c:strRef><c:f>{escape(q)}!${c}$1</c:f></c:strRef></c:tx>'
            '<c:marker><c:symbol val="circle"/><c:size val="4"/></c:marker>'
            f'<c:xVal><c:numRef><c:f>{escape(q)}!$C$2:$C${nrows + 1}</c:f></c:numRef></c:xVal>'
            f'<c:yVal><c:numRef><c:f>{escape(q)}!${c}$2:${c}${nrows + 1}</c:f></c:numRef></c:yVal>'
            '<c:smooth val="0"/></c:ser>')
    rich = ('<c:tx><c:rich><a:bodyPr/><a:p><a:r><a:t>{}</a:t></a:r></a:p></c:rich></c:tx>')
    return ('<?xml version="1.0" encoding="UTF-8" standalone="yes"?>'
            '<c:chartSpace xmlns:c="http://schemas.openxmlformats.org/drawingml/2006/chart" '
            'xmlns:a="http://schemas.openxmlformats.org/drawingml/2006/main" '
            'xmlns:r="http://schemas.openxmlformats.org/officeDocument/2006/relationships">'
            f'<c:chart><c:title>{rich.format(escape(title))}<c:overlay val="0"/></c:title>'
            '<c:autoTitleDeleted val="0"/><c:plotArea><c:layout/>'
            f'<c:scatterChart><c:scatterStyle val="lineMarker"/><c:varyColors val="0"/>'
            f'{"".join(series)}<c:axId val="1"/><c:axId val="2"/></c:scatterChart>'
            '<c:valAx><c:axId val="1"/><c:scaling><c:orientation val="minMax"/>'
            + (f'<c:max val="{hi!r}"/><c:min val="{lo!r}"/>' if lo is not None else '')
            + '</c:scaling>'
            '<c:delete val="0"/><c:axPos val="b"/><c:majorGridlines/>'
            f'<c:numFmt formatCode="{fmt}" sourceLinked="0"/>'
            '<c:tickLblPos val="low"/><c:crossAx val="2"/><c:crosses val="autoZero"/>'
            '<c:crossBetween val="midCat"/></c:valAx>'
            '<c:valAx><c:axId val="2"/><c:scaling>'
            + ('<c:logBase val="10"/>' if log else '')
            + '<c:orientation val="minMax"/>'
            + (f'<c:max val="{yhi!r}"/><c:min val="{ylo!r}"/>' if ylo is not None else '')
            + '</c:scaling>'
            '<c:delete val="0"/><c:axPos val="l"/><c:majorGridlines/>'
            '<c:numFmt formatCode="General" sourceLinked="1"/><c:tickLblPos val="nextTo"/>'
            '<c:crossAx val="1"/><c:crosses val="min"/><c:crossBetween val="midCat"/>'
            '</c:valAx></c:plotArea><c:legend><c:legendPos val="r"/><c:overlay val="0"/>'
            '</c:legend><c:plotVisOnly val="1"/><c:dispBlanksAs val="gap"/></c:chart>'
            '</c:chartSpace>')


def drawing_xml(at_col, rows, charts):
    anchors = "".join(anchor_xml(at_col, 1 + k * (rows + 1), rows, k + 1)
                      for k in range(charts))
    return ('<?xml version="1.0" encoding="UTF-8" standalone="yes"?>'
            '<xdr:wsDr xmlns:xdr="http://schemas.openxmlformats.org/drawingml/2006/spreadsheetDrawing" '
            'xmlns:a="http://schemas.openxmlformats.org/drawingml/2006/main" '
            'xmlns:c="http://schemas.openxmlformats.org/drawingml/2006/chart" '
            'xmlns:r="http://schemas.openxmlformats.org/officeDocument/2006/relationships">'
            f'{anchors}</xdr:wsDr>')


def anchor_xml(at_col, row, rows, k):
    return (f'<xdr:twoCellAnchor><xdr:from><xdr:col>{at_col}</xdr:col><xdr:colOff>0</xdr:colOff>'
            f'<xdr:row>{row}</xdr:row><xdr:rowOff>0</xdr:rowOff></xdr:from>'
            f'<xdr:to><xdr:col>{at_col + 14}</xdr:col><xdr:colOff>0</xdr:colOff>'
            f'<xdr:row>{row + rows}</xdr:row><xdr:rowOff>0</xdr:rowOff></xdr:to>'
            f'<xdr:graphicFrame macro=""><xdr:nvGraphicFramePr><xdr:cNvPr id="{k + 1}" name="Chart {k}"/>'
            '<xdr:cNvGraphicFramePr/></xdr:nvGraphicFramePr>'
            '<xdr:xfrm><a:off x="0" y="0"/><a:ext cx="0" cy="0"/></xdr:xfrm>'
            '<a:graphic><a:graphicData uri="http://schemas.openxmlformats.org/drawingml/2006/chart">'
            f'<c:chart r:id="rId{k}"/></a:graphicData></a:graphic></xdr:graphicFrame>'
            '<xdr:clientData/></xdr:twoCellAnchor>')


def rels(items):
    body = "".join(f'<Relationship Id="{i}" Type="{t}" Target="{escape(g)}"/>'
                   for i, t, g in items)
    return ('<?xml version="1.0" encoding="UTF-8" standalone="yes"?>'
            '<Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships">'
            f'{body}</Relationships>')


R = "http://schemas.openxmlformats.org/officeDocument/2006/relationships/"
CT = "application/vnd.openxmlformats-officedocument."


def write_xlsx(path, history):
    # Sheets in the order the tables and metrics first appear.
    keys, programs = [], {}
    for c in history:
        for table, program, metric, _ in c["rows"]:
            if (table, metric) not in programs:
                keys.append((table, metric))
                programs[(table, metric)] = []
            if program not in programs[(table, metric)]:
                programs[(table, metric)].append(program)

    sheets = []  # (name, xml, chart xml or None)
    used = set()
    long = [["n", "commit", "date", "subject", "table", "program", "metric", "value"]]
    for n, c in enumerate(history, 1):
        for table, program, metric, v in c["rows"]:
            long.append([n, c["hash"], c["date"], c["subject"], table, program, metric, v])

    for table, metric in keys:
        progs = programs[(table, metric)]
        name = sheet_name(table, metric, used)
        # Columns: n, commit, date, subject, the programs' values, a gap, then
        # each program as a percentage of its first nonzero value.
        grid = [["n", "commit", "date", "subject"] + progs + [None]
                + [f"{p} %" for p in progs]]
        base = {}
        for n, c in enumerate(history, 1):
            vals = {p: v for t, p, m, v in c["rows"] if (t, m) == (table, metric)}
            if not vals:
                continue
            for p, v in vals.items():
                if v and p not in base:
                    base[p] = v
            rel = [100 * vals[p] / base[p] if p in base and vals.get(p) is not None else None
                   for p in progs]
            grid.append([n, c["hash"], serial(c["date"]) or c["date"], c["subject"]]
                        + [vals.get(p) for p in progs] + [None] + rel)
        nrows, k = len(grid) - 1, len(progs)
        xs = date_range(r[2] for r in grid[1:])
        absolute = [v for r in grid[1:] for v in r[4:4 + k]]
        log = all(v is None or v > 0 for v in absolute)
        title = f"{table}: {metric}"
        charts = [
            chart_xml(title + (" (log scale)" if log else ""), name, progs, nrows, 4, *xs,
                      log=log, **({} if log else dict(zip(("ylo", "yhi"), y_range(absolute))))),
            chart_xml(title + " (% of first value)", name, progs, nrows, 5 + k, *xs,
                      **dict(zip(("ylo", "yhi"), y_range(v for r in grid[1:] for v in r[5 + k:])))),
        ]
        sheets.append((name, sheet_xml(grid, True), charts, 2 * k + 6))
    sheets.append(("data", sheet_xml(long, False), [], 0))

    with zipfile.ZipFile(path, "w", zipfile.ZIP_DEFLATED) as z:
        overrides = [('/xl/workbook.xml', CT + "spreadsheetml.sheet.main+xml"),
                     ('/xl/styles.xml', CT + "spreadsheetml.styles+xml")]
        wb_rels, wb_sheets = [], []
        chart_no = 0
        for i, (name, sxml, cxmls, at_col) in enumerate(sheets, 1):
            z.writestr(f"xl/worksheets/sheet{i}.xml", sxml)
            overrides.append((f"/xl/worksheets/sheet{i}.xml",
                              CT + "spreadsheetml.worksheet+xml"))
            wb_rels.append((f"rId{i}", R + "worksheet", f"worksheets/sheet{i}.xml"))
            wb_sheets.append(f'<sheet name="{escape(name)}" sheetId="{i}" r:id="rId{i}"/>')
            if cxmls:
                z.writestr(f"xl/worksheets/_rels/sheet{i}.xml.rels",
                           rels([("rId1", R + "drawing", f"../drawings/drawing{i}.xml")]))
                z.writestr(f"xl/drawings/drawing{i}.xml", drawing_xml(at_col, 20, len(cxmls)))
                overrides.append((f"/xl/drawings/drawing{i}.xml", CT + "drawing+xml"))
                chart_rels = []
                for j, cxml in enumerate(cxmls, 1):
                    chart_no += 1
                    z.writestr(f"xl/charts/chart{chart_no}.xml", cxml)
                    chart_rels.append((f"rId{j}", R + "chart", f"../charts/chart{chart_no}.xml"))
                    overrides.append((f"/xl/charts/chart{chart_no}.xml",
                                      CT + "drawingml.chart+xml"))
                z.writestr(f"xl/drawings/_rels/drawing{i}.xml.rels", rels(chart_rels))
        n = len(sheets)
        wb_rels.append((f"rId{n + 1}", R + "styles", "styles.xml"))
        z.writestr("[Content_Types].xml",
                   '<?xml version="1.0" encoding="UTF-8" standalone="yes"?>'
                   '<Types xmlns="http://schemas.openxmlformats.org/package/2006/content-types">'
                   '<Default Extension="rels" ContentType="application/vnd.openxmlformats-package.relationships+xml"/>'
                   '<Default Extension="xml" ContentType="application/xml"/>'
                   + "".join(f'<Override PartName="{p}" ContentType="{t}"/>' for p, t in overrides)
                   + '</Types>')
        z.writestr("_rels/.rels", rels([("rId1", R + "officeDocument", "xl/workbook.xml")]))
        z.writestr("xl/workbook.xml",
                   '<?xml version="1.0" encoding="UTF-8" standalone="yes"?>'
                   '<workbook xmlns="http://schemas.openxmlformats.org/spreadsheetml/2006/main" '
                   'xmlns:r="http://schemas.openxmlformats.org/officeDocument/2006/relationships">'
                   f'<sheets>{"".join(wb_sheets)}</sheets></workbook>')
        z.writestr("xl/_rels/workbook.xml.rels", rels(wb_rels))
        z.writestr("xl/styles.xml",
                   '<?xml version="1.0" encoding="UTF-8" standalone="yes"?>'
                   '<styleSheet xmlns="http://schemas.openxmlformats.org/spreadsheetml/2006/main">'
                   '<numFmts count="1"><numFmt numFmtId="164" formatCode="yyyy-mm-dd hh:mm"/></numFmts>'
                   '<fonts count="1"><font><sz val="11"/><name val="Calibri"/></font></fonts>'
                   '<fills count="2"><fill><patternFill patternType="none"/></fill>'
                   '<fill><patternFill patternType="gray125"/></fill></fills>'
                   '<borders count="1"><border><left/><right/><top/><bottom/><diagonal/></border></borders>'
                   '<cellStyleXfs count="1"><xf numFmtId="0" fontId="0" fillId="0" borderId="0"/></cellStyleXfs>'
                   '<cellXfs count="2"><xf numFmtId="0" fontId="0" fillId="0" borderId="0" xfId="0"/>'
                   '<xf numFmtId="164" fontId="0" fillId="0" borderId="0" xfId="0" applyNumberFormat="1"/></cellXfs>'
                   '</styleSheet>')
    return chart_no


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("-o", "--out", default="bench-history",
                    help="output path without extension (default: bench-history)")
    ap.add_argument("--no-xlsx", action="store_true", help="write only the CSV")
    args = ap.parse_args()
    out = re.sub(r"\.(csv|xlsx)$", "", args.out)

    history = read_history(sys.stdin.read())
    if not history:
        sys.exit("bench-history: no bench tables found on stdin")
    write_csv(out + ".csv", history)
    msg = f"{len(history)} commits -> {out}.csv"
    if not args.no_xlsx:
        charts = write_xlsx(out + ".xlsx", history)
        msg += f", {out}.xlsx ({charts} charts)"
    print(msg, file=sys.stderr)


if __name__ == "__main__":
    main()
