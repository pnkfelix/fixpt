"""split.py FILE MODULE CUT NEWFILE HEADER: old-style FILE's module items
before item CUT (after its leading type selects) moved to NEWFILE, placed
before FILE, its module `NEWSTEM-module`. Re-exports follow the names;
the converted clients that import moved names from FILE's module are
given the new one too (signature `NEWSTEM-sig`, from the printed types
in fe-check-presplit.txt), and the conductor gives it to them. HEADER is
the new file's first comment, ';;;' lines."""
import sys, re, os, subprocess
import paths
SRC = paths.SRC
T = paths.T
fname, mod, cut, newfile, header = sys.argv[1], sys.argv[2], int(sys.argv[3]), sys.argv[4], sys.argv[5]
stem, newstem = fname[:-3], newfile[:-3]
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
s = open(SRC + fname).read()
st = re.search(r'\(define %s\s+\(module' % mod, s).start(); mo = s.index('(module', st) + 7; en = sexp_end(s, st)
items = []; i = mo
while True:
    while s[i] in ' \n\t': i += 1
    if s[i] == ';': i = s.index('\n', i); continue
    if s[i] == ')': break
    j = sexp_end(s, i); items.append((i, j)); i = j
def is_sel(a, b): return re.match(r'\((define-type|define-effect) \S+ \(select \S+-types \S+\)\)$|\(define \S+ \(with \S+-types \S+\)\)$', s[a:b]) is not None
nsel = 0
while is_sel(*items[nsel]): nsel += 1
assert cut > nsel
# The head runs from the comments before its first item to the comments before item CUT.
def comment_start(p):
    k = s.rfind('\n', 0, p) + 1
    while True:
        pk = s.rfind('\n', 0, k - 1) + 1
        if k > 0 and s[pk:k - 1].lstrip().startswith(';'): k = pk
        else: return k
h0 = comment_start(items[nsel][0]); h1 = items[cut - 1][1]
head = s[h0:h1].rstrip('\n') + '\n'
TOK = re.compile(r"[A-Za-z0-9!$%&*/:<=>?^_~+.@|-]+")
def strip(t): return re.sub(r'"(\\.|[^"\\])*"', '""', re.sub(r';[^\n]*', '', t))
def defs(t):
    t = strip(t); out = set(re.findall(r'^\((?:define\*?|define-type|define-effect|define-datatype) \(?([^\s()]+)', t, re.M))
    out |= set(re.findall(r'\n  \(([^\s()]+) \(subr', t)); return out
moved = defs(head)
rest_items = s[h1:en]
uses_rest = set(TOK.findall(strip(rest_items)))
sels = [s[a:b] for a, b in items[:nsel]]
need_sel = [x for x in sels if re.search(r'^\(\S+ (\S+) ', x).group(1) in set(TOK.findall(strip(head)))]
after = s[en:]
reexp = re.findall(r'^\(define (\S+) \(with %s \1\)\)$' % re.escape(mod), after, re.M)
reexp_new = sorted((set(reexp) | uses_rest) & moved)
new_mod = newstem + '-module'
types_load = re.search(r'^\(define (%s-types) \(load-module "fx26:%s-types.fx"\)\)$' % (re.escape(stem), re.escape(stem)), s, re.M)
newtext = header.rstrip('\n') + '\n\n'
if types_load:
    newtext += (';; Its types (`%s-types.fx`, its file\'s after it), loaded before the\n;; module so that they are not among its values; the module names what it\n;; uses of them.\n%s\n' % (stem, types_load.group(0)))
newtext += (';; A module (`TODO.md` §34: the front end into modules, a file at a time);\n'
            ';; what other files use re-exported after it.\n(define %s (module\n' % new_mod
            + ''.join(x + '\n' for x in need_sel) + '\n' + head.rstrip('\n') + '))\n\n'
            + ''.join('(define %s (with %s %s))\n' % (n, new_mod, n) for n in reexp_new))
open(SRC + newfile, 'w').write(newtext)
after2 = '\n'.join(l for l in after.split('\n') if not (re.match(r'^\(define (\S+) \(with %s \1\)\)$' % re.escape(mod), l) and re.match(r'^\(define (\S+)', l).group(1) in moved))
open(SRC + fname, 'w').write(s[:h0] + s[h1:en] + after2)
print(len(moved), 'names moved;', len(reexp_new), 're-exported by the new file')
# lib.rs: before FILE, in its list.
L = open(SRC + 'lib.rs').read()
m = re.search(r'^    \("%s", (.*)\),\n' % re.escape(fname), L, re.M)
arr_m = list(re.finditer(r'pub const (\w+): \[\(&str, &str\); (\d+)\] = \[', L[:m.start()]))[-1]
arr = arr_m.group(1); idx = L[arr_m.end():m.start()].count('\n    ("')
L = L[:m.start()] + '    ("%s", include_str!("%s")),\n' % (newfile, newfile) + L[m.start():]
L = L.replace(arr_m.group(0), arr_m.group(0).replace('; %s]' % arr_m.group(2), '; %d]' % (int(arr_m.group(2)) + 1)), 1)
if arr != 'FRONT_END_FILES':
    def renum(mm):
        j = int(mm.group(1)); return '    %s[%d],' % (arr, j + 1 if j >= idx else j)
    L = re.sub(r'    %s\[(\d+)\],' % arr, renum, L)
    L = L.replace('    %s[%d],\n' % (arr, idx + 1), '    %s[%d],\n    %s[%d],\n' % (arr, idx, arr, idx + 1), 1)
    mm = re.search(r'pub const FRONT_END_FILES: \[\(&str, &str\); (\d+)\]', L)
    L = L.replace(mm.group(0), mm.group(0).replace(mm.group(1), str(int(mm.group(1)) + 1)))
open(SRC + 'lib.rs', 'w').write(L)
# The converted clients.
clients = {}
for f in os.listdir(SRC):
    if not f.endswith('.fx') or f.endswith('-types.fx') or f in (fname, newfile): continue
    t = open(SRC + f).read()
    used = [n for n in sorted(moved) if re.search(r'^\(define %s \(with %s %s\)\)$' % (re.escape(n), re.escape(stem), re.escape(n)), t, re.M)]
    if used: clients[f] = used
names = sorted(set(n for v in clients.values() for n in v))
if names:
    r = subprocess.run(['python3', T + 'x/mksig.py', T + 'fe-check-presplit.txt', mod, newstem + '-sig', newstem + '-types.fx',
                        ', '.join('`%s`' % c for c in sorted(clients))] + names, capture_output=True, text=True)
    print(r.stdout.strip(), r.stderr.strip()[-300:])
    tt = open(SRC + newstem + '-types.fx').read().replace('its `%s`' % mod, 'its `%s`' % new_mod)
    open(SRC + newstem + '-types.fx', 'w').write(tt)
    # Out of FILE's signature.
    tf = SRC + stem + '-types.fx'; tt = open(tf).read()
    k = tt.index('(define-type %s-sig' % stem); e = sexp_end(tt, k); sig = tt[k:e]
    mo2 = sig.index('(moduleof') + len('(moduleof'); i = mo2; its = []
    while True:
        while sig[i] in ' \n': i += 1
        if sig[i] == ')': break
        j = sexp_end(sig, i); its.append(sig[i:j]); i = j
    keep = [it for it in its if re.match(r'\(val ([^\s()]+)', it).group(1) not in moved]
    ind = ' ' * (sig.index(its[0]) - sig.rfind('\n', 0, sig.index(its[0])) - 1) if '\n' in sig[:sig.index(its[0])] else ' ' * 12
    newsig = sig[:sig.index(its[0])] + ('\n' + ind).join(keep) + '))'
    tt = tt[:k] + newsig + tt[e:]; open(tf, 'w').write(tt)
    print(len(its) - len(keep), 'out of', stem + '-sig')
    C = open(SRC + 'conductor.fx').read()
    for f, used in clients.items():
        t = open(SRC + f).read()
        for n in used: t = t.replace('(define %s (with %s %s))' % (n, stem, n), '(define %s (with %s %s))' % (n, newstem, n))
        t = re.sub(r'(\n       \(%s-types \(load-module "fx26:%s-types.fx"\)\))' % (re.escape(stem), re.escape(stem)),
                   r'\1\n       (%s-types (load-module "fx26:%s-types.fx"))' % (newstem, newstem), t, 1)
        m2 = re.search(r'\n(\s+)\((\S+) \(select (\S+) (\S+)\)\)\)\n    \(module', t)
        t = t[:m2.start()] + '\n%s(%s (select %s %s))\n%s(%s (select %s-types %s-sig)))\n    (module' % (
            m2.group(1), m2.group(2), m2.group(3), m2.group(4), m2.group(1), newstem, newstem, newstem) + t[m2.end():]
        open(SRC + f, 'w').write(t)
        b = f[:-3]
        k = C.index('(%s\n' % b); k2 = C.index('))\n', k)
        line_start = C.rfind('\n', 0, k2) + 1
        if k2 - line_start + len(' ' + new_mod) + 2 > 100:
            C = C[:k2] + '\n           ' + new_mod + C[k2:]
        else:
            C = C[:k2] + ' ' + new_mod + C[k2:]
        print(f, len(used), 'names from', newstem)
    open(SRC + 'conductor.fx', 'w').write(C)
    # Register the new types file.
    L = open(SRC + 'lib.rs').read()
    tfn = newstem + '-types.fx'
    if '"%s"' % tfn not in L:
        const = re.sub(r'[^A-Z0-9]', '_', tfn[:-3].upper())
        k = L.index("/// Hash tables' types: a module file of no state")
        L = L[:k] + '/// `%s`: types and signatures, a module file of no state (`TODO.md` §68).\npub const %s: &str = include_str!("%s");\n\n' % (tfn, const, tfn) + L[k:]
        k = L.index('pub const FRONT_END_MODULES'); e = L.index('\n];', k)
        L = L[:e + 1] + '    ("%s", %s),\n' % (tfn, const) + L[e + 1:]
        mm = re.search(r'pub const FRONT_END_MODULES: \[\(&str, &str\); (\d+)\]', L)
        L = L.replace(mm.group(0), mm.group(0).replace(mm.group(1), str(int(mm.group(1)) + 1)))
        open(SRC + 'lib.rs', 'w').write(L)
