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
def cstart(p):
    k = s.rfind('\n', 0, p) + 1
    while True:
        pk = s.rfind('\n', 0, k - 1) + 1
        if k > 0 and s[pk:k - 1].lstrip().startswith(';'): k = pk
        else: return k
spans = [(cstart(a), b) for a, b in items]
lv = sorted(leaf)
moved = ''.join(s[spans[k][0]:spans[k][1]] + '\n' for k in lv)
out = s[:spans[0][0]] + moved
prev = spans[0][0]
rest = ''
for k in range(len(items)):
    if k in leaf:
        rest += s[prev:spans[k][0]]; prev = spans[k][1]
        # drop the newline after a moved item
        if s[prev:prev+1] == '\n': prev += 1
rest += s[prev:]
open(SRC + f, 'w').write(out + rest)
print(len(lv), 'moved first')
