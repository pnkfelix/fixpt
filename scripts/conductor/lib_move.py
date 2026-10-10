"""lib_move.py FILE: in lib.rs, FILE moved from the front end's files to
its module files; each types file not yet there registered too."""
import sys, re, os
import paths
SRC = paths.SRC
fname = sys.argv[1]
p = SRC + 'lib.rs'; s = open(p).read()
def bump(s, arr, by):
    m = re.search(r'pub const %s: \[\(&str, &str\); (\d+)\]' % arr, s)
    return s.replace(m.group(0), m.group(0).replace(m.group(1), str(int(m.group(1)) + by)), 1)
m = re.search(r'^    \("%s", (.*)\),\n' % re.escape(fname), s, re.M)
entry = m.group(0); val = m.group(1)
# Which array it is in, and its index there.
arr_m = list(re.finditer(r'pub const (\w+): \[\(&str, &str\); \d+\] = \[', s[:m.start()]))[-1]
arr = arr_m.group(1)
idx = s[arr_m.end():m.start()].count('\n    ("')
s = s[:m.start()] + s[m.end():]
s = bump(s, arr, -1)
if arr != 'FRONT_END_FILES':
    # FRONT_END_FILES names it by index: gone, the later ones one less.
    s = s.replace('    %s[%d],\n' % (arr, idx), '', 1)
    def renum(mm):
        j = int(mm.group(1)); return '    %s[%d],' % (arr, j - 1 if j > idx else j)
    s = re.sub(r'    %s\[(\d+)\],' % arr, renum, s)
    s = bump(s, 'FRONT_END_FILES', -1)
# Its text a constant, if it was written in place.
if val.startswith('include_str!'):
    const = re.sub(r'[^A-Z0-9]', '_', fname[:-3].upper())
    k = s.index("/// Hash tables' types: a module file of no state")
    s = s[:k] + '/// `%s`: a `load-input` file, which the conductor applies (`TODO.md` §68).\npub const %s: &str = %s;\n\n' % (fname, const, val) + s[k:]
    val = const
new = ['    ("%s", %s),\n' % (fname, val)]
# Types files not yet registered.
for f in sorted(os.listdir(SRC)):
    if f.endswith('-types.fx') and ('"%s"' % f) not in s:
        const = re.sub(r'[^A-Z0-9]', '_', f[:-3].upper())
        k = s.index("/// Hash tables' types: a module file of no state")
        s = s[:k] + '/// `%s`: types and signatures, a module file of no state (`TODO.md` §68).\npub const %s: &str = include_str!("%s");\n\n' % (f, const, f) + s[k:]
        new.insert(0, '    ("%s", %s),\n' % (f, const))
k = s.index('pub const FRONT_END_MODULES')
e = s.index('\n];', k)
s = s[:e + 1] + ''.join(new) + s[e + 1:]
s = bump(s, 'FRONT_END_MODULES', len(new))
open(p, 'w').write(s)
print('moved', fname, 'from', arr, '[%d]' % idx, '; registered', len(new) - 1, 'types files')
