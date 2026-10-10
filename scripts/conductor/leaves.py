"""seams.py FILE MODULE: where a module's top items can be cut in two, every
item before using nothing defined after; the line, the lines after, and how
many names before the items after use."""
import sys, re
import paths
SRC = paths.SRC
f, mod = sys.argv[1], sys.argv[2]
s = open(SRC + f).read()
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
st = re.search(r'\(define %s\s+\(module' % mod, s).start(); mo = s.index('(module', st) + 7; en = sexp_end(s, st)
items = []; i = mo
while True:
    while s[i] in ' \n\t': i += 1
    if s[i] == ';': i = s.index('\n', i); continue
    if s[i] == ')': break
    j = sexp_end(s, i); items.append((i, j)); i = j
TOK = re.compile(r"[A-Za-z0-9!$%&*/:<=>?^_~+.@|-]+")
def strip(t): return re.sub(r'"(\\.|[^"\\])*"', '""', re.sub(r';[^\n]*', '', t))
def defs(t):
    t = strip(t); out = set(re.findall(r'^\((?:define\*?|define-type|define-effect|define-datatype) \(?([^\s()]+)', t))
    if t.startswith('(define-rec'): out |= set(re.findall(r'\n  \(([^\s()]+) \(subr', t))
    return out
D = [defs(s[a:b]) for a, b in items]; U = [set(TOK.findall(strip(s[a:b]))) for a, b in items]
line = lambda p: s[:p].count('\n') + 1
endl = line(en)
# Items using no name defined by a non-leaf item: grow the leaf set to a fixpoint.
alld = set().union(*D)
leaf = set()
changed = True
while changed:
    changed = False
    for k in range(len(items)):
        if k in leaf: continue
        others = set().union(*[D[j] for j in range(len(items)) if j not in leaf and j != k]) if True else set()
        if not (U[k] & (others - D[k])) and not (U[k] & D[k] - D[k]):
            # uses only leaves' names or outside names (its own names allowed: self recursion)
            leaf.add(k); changed = True
tot = 0
for k in sorted(leaf):
    a, b = items[k]; n = s[a:b].count('\n') + 1; tot += n
    print(k, line(a), n, sorted(D[k])[:3])
print('leaf lines', tot, 'of', len(items), 'items', len(leaf), 'leaves')
