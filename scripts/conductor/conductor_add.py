"""conductor_add.py NAME FILE COMMENT ARG...: in conductor.fx, make module
NAME first, `((load-input "fx26:FILE") ARG...)`, and give it where the
old top-level `MODULE` (the file's) was given."""
import sys, re
import paths
SRC = paths.SRC
name, fname, comment, old, args = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4], sys.argv[5:]
p = SRC + 'conductor.fx'; s = open(p).read()
k = s.index('  (let* (') + len('  (let* (')
# Where the old module was given, the new one is.
body = s[k:]
body = re.sub(r'(?<![\w-])%s(?![\w-])' % re.escape(old), name, body)
call = '((load-input "fx26:%s") %s)' % (fname, ' '.join(args))
one = '         (%s %s)' % (name, call)
if len(one) > 100:
    # The arguments wrapped at 100 columns, under the call.
    lines = ['         (%s' % name, '          ((load-input "fx26:%s")' % fname]
    cur = '           '
    for a in args:
        if len(cur) + len(a) + 1 > 97 and cur.strip():
            lines.append(cur.rstrip()); cur = '           '
        cur += a + ' '
    lines.append(cur.rstrip() + '))')
    one = '\n'.join(lines)
first = body.lstrip()
s = s[:k] + ';; %s\n' % comment + one + '\n         ' + first
open(p, 'w').write(s)
print(open(p).read()[s.index('(let* ('):s.index('(let* (') + 600])
