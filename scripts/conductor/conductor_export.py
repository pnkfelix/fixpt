"""conductor_export.py MODULE NAME...: the conductor names each NAME of
module MODULE at top level, for Rust and `bootstrap.fx`."""
import sys
import paths
SRC = paths.SRC
mod, names = sys.argv[1], sys.argv[2:]
p = SRC + 'conductor.fx'; s = open(p).read()
k = s.index('    (product ')
e = s.index(')))))', k) if ')))))\n' in s[k:] else None
# The product's last field closes it, the let*, and the define.
end = s.index('\n\n', k)
prod = s[k:end]
assert prod.endswith(')))))'), prod[-20:]
fields = ''.join('\n             (%s (with %s %s))' % (n, mod, n) for n in names)
prod = prod[:-3] + fields + ')))'
s = s[:k] + prod + s[end:]
s = s.rstrip('\n') + '\n' + ''.join('(define %s (extract front-end-entries %s))\n' % (n, n) for n in names)
open(p, 'w').write(s)
print(s[k:k + len(prod) + 400][-700:])
