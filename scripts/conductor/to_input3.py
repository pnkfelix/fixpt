"""to_input3.py FILE [--check-output OUT]: front-end FILE (a top-level
`(define X-module (module ...))` and its re-exports) made a `load-input`
file. The names it uses of earlier files: types, effects and datatype
constructors from their types files, loaded in its `let*`; values from
the modules it is given, each typed by `D-sig` in `D-types.fx`, which is
(re)made with them (`mksig.py`). Prints what the conductor gives it."""
import sys, re, subprocess, os
import paths
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from registry2 import table, ctors, SRC
D = os.path.dirname(os.path.abspath(__file__))
ROOT = paths.ROOT
fname = sys.argv[1]
OUT = paths.T + 'fe-check.txt'
BOGUS = {'define', 'define-type', 'define-datatype', 'define-effect', 'listof', 'new', 'ref', 'pairof', 'lambda', 'subr'}
SPECIAL = {'table.fx': ('tables', 'tables-sig', 'table-types.fx')}
def dep_info(f):
    if f in SPECIAL: return SPECIAL[f]
    if '#' in f:
        # A module `reader.fx` names at top level: its signature in
        # `reader-types.fx`.
        m = f.split('#')[1]; stem = m[:-len('-module')]
        return (stem, stem + '-sig', 'reader-types.fx')
    stem = f[:-3]
    return (stem, stem + '-sig', stem + '-types.fx')
def module_of(f):
    if '#' in f: return f.split('#')[1]
    if not os.path.exists(SRC + f): return None
    m = re.search(r'^\(define (\S+)\s+\(module', open(SRC + f).read(), re.M)
    return m.group(1) if m else None
def sexp_end(t, i):
    d = 0; instr = False
    while True:
        c = t[i]
        if instr:
            if c == '\\': i += 1
            elif c == '"': instr = False
        elif c == '"': instr = True
        elif c == ';': i = t.index('\n', i); continue
        elif t.startswith('#\\', i): i += 3; continue
        elif c == '(': d += 1
        elif c == ')':
            d -= 1
            if d == 0: return i + 1
        i += 1
reg = table()
CT = ctors()
out = subprocess.run(['python3', D + '/deps.py', fname], capture_output=True, text=True, cwd=ROOT).stdout
own_mod = module_of(fname)
s = open(SRC + fname).read()
own_types = set(re.findall(r'^\((?:define-type|define-effect) (\S+) \(select ', s, re.M)) | set(re.findall(r'^\(define (\S+) \(with \S+-types \S+\)\)', s, re.M))
type_imports = {}   # var -> (load, [(kind, name)])
values = {}         # dep file -> [names]
for l in out.splitlines():
    if l.startswith('--'): continue
    parts = l.split(' ')
    f, ns = parts[0], parts[2:]
    dtext = re.sub(r';[^\n]*', '', open(SRC + f).read()) if os.path.exists(SRC + f) else ''
    for n in ns:
        if n in BOGUS: continue
        # A name may be a type and a value both: they are apart.
        q = re.escape(n)
        as_value = bool(module_of(f)) and bool(re.search(r'^(?:\(define\*? %s (?!\(with )|  \(%s \(subr )' % (q, q), dtext, re.M))
        if n in reg and n not in own_types:
            kind, tf, v, ld = reg[n]
            type_imports.setdefault(v, (ld, []))[1].append((kind, n))
            if kind != 'ctor' and n in CT:
                # A type, and a constructor of the same name elsewhere.
                k2, tf2, v2, ld2 = CT[n]
                type_imports.setdefault(v2, (ld2, []))[1].append(('ctor', n))
            elif kind != 'ctor' and as_value:
                values.setdefault(f, []).append(n)
        elif n not in reg:
            values.setdefault(f, []).append(n)
# A type the file uses that it defines as a value only (types and values
# are apart), which the dependency scan took for the file's own.
toks = set(re.findall(r"[A-Za-z0-9!$%&*/:<=>?^_~+.@|-]+", re.sub(r'"(\\.|[^"\\])*"', '""', re.sub(r';[^\n]*', '', s))))
own_type_defs = set(re.findall(r'^\((?:define-type|define-effect|define-datatype) \(?([^\s()]+)', s, re.M))
have = {n for _, (_, ns) in type_imports.items() for _, n in ns}
for n in sorted(toks):
    if n in reg and reg[n][0] in ('type', 'effect') and n not in own_types and n not in own_type_defs and n not in have:
        kind, tf, v, ld = reg[n]
        if re.search(r'^\(define\*? %s ' % re.escape(n), s, re.M):
            type_imports.setdefault(v, (ld, []))[1].append((kind, n)); have.add(n)
            print('type beside a value of its name:', n)
# `reader.fx`'s names are its modules' (the parser's, the reader's),
# re-exported: each from the module it names.
if 'reader.fx' in values:
    rd = open(SRC + 'reader.fx').read()
    for n in values.pop('reader.fx'):
        mm = re.search(r'^\(define %s \(with (\S+-module) %s\)\)$' % (re.escape(n), re.escape(n)), rd, re.M)
        if mm: values.setdefault('reader.fx#' + mm.group(1), []).append(n)
        else: print('skipped, not a module\'s in reader.fx:', n)
# A file with no module gives no values: a name of its seen here is a local
# one of the same spelling (the check finds any that is not).
for f in [f for f in values if not module_of(f)]:
    print('skipped, no module in %s: %s' % (f, ' '.join(values.pop(f))))
# The signatures of the modules it is given, with what it uses.
for f, ns in values.items():
    p, sig, tf = dep_info(f)
    r = subprocess.run(['python3', D + '/mksig.py', OUT, module_of(f), sig, tf, '`%s`' % fname] + ns, capture_output=True, text=True)
    print(r.stdout.strip() or r.stderr.strip())
    if r.returncode: sys.exit('mksig failed for ' + f)
# The file.
start = re.search(r'\(define %s\s+\(module' % re.escape(own_mod), s).start()
end = sexp_end(s, start)
head = s[:start]
body = s[s.index('(module', start) + len('(module'):end - 2]
lines = head.split('\n'); intro = []; k = 0
while k < len(lines) and (lines[k].startswith(';;;') or lines[k] == ''):
    intro.append(lines[k]); k += 1
rest = '\n'.join(lines[k:])
rest = re.sub(r";; A module \(`TODO\.md` §34[^\n]*\n;; what other files use re-exported after it\.\n", '', rest)
rest = re.sub(r";; Its types \(`[^`]+`\), loaded before the module so that they are\n;; not among its values; the module names what it uses of them\.\n", '', rest)
loads = []; cm = []; i = 0
while i < len(rest):
    if rest[i] in ' \n': i += 1; continue
    if rest[i] == ';':
        e = rest.index('\n', i); cm.append(rest[i:e]); i = e + 1; continue
    e = sexp_end(rest, i); f_ = rest[i:e]
    m = re.match(r'\(define (\S+) (.*)\)$', f_, re.S)
    assert m and 'load-module' in f_, f_[:80]
    loads.append((cm, m.group(1), m.group(2))); cm = []; i = e
have_vars = {v for _, v, _ in loads}
for v, (ld, _) in type_imports.items():
    if v not in have_vars: loads.append(([], v, ld)); have_vars.add(v)
params = []
for f in values:
    p, sig, tf = dep_info(f)
    tv = tf[:-3]
    if tv not in have_vars:
        loads.append(([], tv, '(load-module "fx26:%s")' % tf)); have_vars.add(tv)
    params.append('(%s (select %s %s))' % (p, tv, sig))
m = re.match(r'((?:\s*\((?:define-effect|define-type) \S+ \(select [^()]*\)\)\n|\s*\(define \S+ \(with \S+-types \S+\)\)\n)*)', body)
selects, items = m.group(1), body[m.end():]
o = intro
if not o or o[-1] != '': o.append('')
o.append(';; Its types, those it uses of the files before it, and the signatures of')
o.append(';; what it is given.')
for n, (cms, name, e) in enumerate(loads):
    for c in cms: o.append(('       ' if n else '') + c)
    o.append(('(let* (' if n == 0 else '       ') + '(%s %s)' % (name, e) + (')' if n == len(loads) - 1 else ''))
o.append("  ;; What it is given: the modules of the files before it that it uses.")
if params:
    o.append('  (lambda (' + params[0] + ('' if len(params) > 1 else ')'))
    for k, p in enumerate(params[1:], 1):
        o.append('           ' + p + (')' if k == len(params) - 1 else ''))
o.append('    (module')
o.append(selects.strip('\n'))
if type_imports:
    o.append(';; The types it uses of the files before it.')
    for v, (_, ns) in type_imports.items():
        for kind, n in ns:
            o.append({'type': '(define-type %s (select %s %s))', 'effect': '(define-effect %s (select %s %s))',
                      'ctor': '(define %s (with %s %s))'}[kind] % (n, v, n))
o.append(';; What it uses of the modules it is given.')
for f, ns in values.items():
    p = dep_info(f)[0]
    for n in ns: o.append('(define %s (with %s %s))' % (n, p, n))
# The closers of the module, the lambda and the `let*`; on a line of their
# own where the last line would pass 100 columns.
close = ')))' if params else '))'
if len(items.rstrip().split('\n')[-1]) + len(close) > 100:
    o.append(items.rstrip() + '\n;; The module, the lambda given its modules, and the loads, closed.\n' + close)
else:
    o.append(items.rstrip() + close)
text = '\n'.join(o) + '\n'
text = re.sub(r'\n\n\n+', '\n\n', text)
open(SRC + fname, 'w').write(text)
print('conductor gives:', ' '.join(module_of(f) or f for f in values))
print('imports: types', sum(len(ns) for _, ns in type_imports.values()), 'values', sum(len(v) for v in values.values()))
