"""mksig.py CHECK-OUTPUT MODULE SIG TYPES-FILE CLIENT NAME...: (re)write
`(define-type SIG (moduleof (val NAME TYPE) ...))` in TYPES-FILE, the
names those already there and NAME..., each TYPE as MODULE's printed type
in CHECK-OUTPUT has it; importing, before it, the type names it uses that
the file does not define, from their types files. CLIENT names who uses
it, for the comment of a new signature."""
import sys, re, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from registry2 import table, SRC
from pp import layout
out, mod, sig, tfile, client, names = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4], sys.argv[5], sys.argv[6:]
path = SRC + tfile
text = open(path).read() if os.path.exists(path) else None
def sexp_end(s, i):
    d = 0; instr = False
    while True:
        c = s[i]
        if instr:
            if c == '\\': i += 1
            elif c == '"': instr = False
        elif c == '"': instr = True
        elif c == ';' :
            i = s.index('\n', i); continue
        elif c == '(': d += 1
        elif c == ')':
            d -= 1
            if d == 0: return i + 1
        i += 1
old = set(); old_items = []
if text and ('(define-type %s\n' % sig) in text:
    k = text.index('(define-type %s\n' % sig); e = sexp_end(text, k)
    old = set(re.findall(r'\(val ([^\s()]+)\s', text[k:e]))
    # Its entries as written, kept.
    mo = text.index('(moduleof', k) + len('(moduleof')
    i = mo
    while True:
        while text[i] in ' \n': i += 1
        if text[i] == ')': break
        j = sexp_end(text, i); old_items.append(text[i:j]); i = j
want = set(names) - old
line = next(l for l in open(out) if l.startswith('define %s : ' % mod))
vals = []
for m in re.finditer(r'\(val (\S+) ', line):
    n = m.group(1)
    if n in want:
        j = m.end()
        e = sexp_end(line, j) if line[j] == '(' else j + re.match(r'[^\s()]+', line[j:]).end()
        vals.append((n, line[j:e]))
missing = want - {n for n, _ in vals}
if missing: sys.exit('not in %s: %s' % (mod, ' '.join(sorted(missing))))
items = old_items + [layout('(val %s %s)' % v, 12) for v in vals]
if not vals and old_items: print(sig, 'has them all'); sys.exit(0)
body = '(define-type %s\n' % sig + '\n'.join(('  (moduleof ' if k == 0 else '            ') + it for k, it in enumerate(items)) + '))'
# Type names it uses that the file does not have.
reg = table()
have = set(re.findall(r'^\((?:define-type|define-effect|define-datatype) \(?(\S+)', text or '', re.M))
# The names after `(val`, values, are not uses of types.
toks = set(re.findall(r"[A-Za-z0-9!$%&*/:<=>?^_~+.@-]+", re.sub(r'\(val \S+', '(val', body)))
imports = []; vars_have = set(re.findall(r'^\(define (\S+) \(+(?:proj )?\(?load-module', text or '', re.M))
for t in sorted(toks):
    if t in have or t not in reg or reg[t][0] == 'ctor' or reg[t][1] == tfile: continue
    kind, f, v, l = reg[t]
    if v not in vars_have:
        imports.append('(define %s %s)' % (v, l)); vars_have.add(v)
    imports.append('(%s %s (select %s %s))' % ('define-effect' if kind == 'effect' else 'define-type', t, v, t))
    have.add(t)
block = (';; The types it names, from the files that define them.\n' + '\n'.join(imports) + '\n' if imports else '') + body
if text is None:
    stem = tfile[:-len('-types.fx')]
    text = (';;; The signature of `%s.fx`, its `%s`,\n'
            ';;; as its clients use it (`TODO.md` §68): a module file of no state.\n\n' % (stem, mod))
if ('(define-type %s\n' % sig) in text:
    # Kept as written, the new entries put after the last, as it is put.
    k = text.index('(define-type %s\n' % sig); e = sexp_end(text, k)
    last = text.rfind('(val ', k, e)
    ind = last - (text.rfind('\n', 0, last) + 1)
    new = ''.join('\n' + ' ' * ind + layout('(val %s %s)' % v, ind) for v in vals)
    text = text[:e - 2] + new + text[e - 2:]
    if imports:
        k = text.index('(define-type %s\n' % sig)
        text = text[:k] + ';; The types it names, from the files that define them.\n' + '\n'.join(imports) + '\n' + text[k:]
else:
    if ';;; ------------------------------------------------------------ signatures' not in text:
        text = text.rstrip('\n') + '\n\n;;; ------------------------------------------------------------ signatures\n'
    words = client.split(', '); lines = []; cur = ';; What its clients use of it ('
    for k, w in enumerate(words):
        piece = w + (', ' if k < len(words) - 1 else ').')
        if len(cur) + len(piece.rstrip()) > 80: lines.append(cur.rstrip()); cur = ';; '
        cur += piece
    lines.append(cur.rstrip())
    text = text.rstrip('\n') + '\n\n' + '\n'.join(lines) + '\n' + block + '\n'
open(path, 'w').write(text)
print(sig, len(vals), 'vals;', len(imports), 'import lines')
