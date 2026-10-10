import re,sys
s=sys.stdin.read(); bad=[]
for m in re.finditer(r'pub const (\w+): \[\(&str, &str\); (\d+)\] = \[\n(.*?)\n\];', s, re.S):
    if 'pub const' in m.group(3): continue
    n=len([l for l in m.group(3).split('\n') if l.strip() and not l.strip().startswith('//')])
    if n!=int(m.group(2)): bad.append('%s %s!=%d'%(m.group(1),m.group(2),n))
print(sys.argv[1], 'BAD '+' '.join(bad) if bad else 'ok')
