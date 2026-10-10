import re,subprocess,sys
import paths
ROOT=paths.ROOT; src=paths.SRC
r=open(src+'reader.fx').read()
cond=open(src+'conductor.fx').read(); boot=open(src+'bootstrap.fx').read()
rs=subprocess.run(['git','grep','-h','-o','"[^"]*"','--','*.rs'],capture_output=True,text=True,cwd=ROOT).stdout
tests=subprocess.run(['git','grep','-h','-e','.','--','crates/fixpt-fx26/tests/programs','crates/fixpt-cli/tests'],capture_output=True,text=True,cwd=ROOT).stdout
C='A-Za-z0-9!$%&*/:<=>?^_~+.@-'
def tok(n): return '(?<![' + C + '])' + re.escape(n) + '(?![' + C + '])'
outside=cond+'\n'+boot+'\n'+rs+'\n'+tests
lines=r.split('\n'); dropped=[]
while True:
    body='\n'.join(lines)
    gone=None
    for i,l in enumerate(lines):
        m=re.match(r'\(define(?:-type|-effect)? (\S+) ',l)
        if not m: continue
        n=m.group(1)
        rest='\n'.join(lines[:i]+lines[i+1:])
        if re.search(tok(n),outside) or re.search(tok(n),re.sub(r';[^\n]*','',rest)): continue
        gone=i; dropped.append(n); break
    if gone is None: break
    del lines[gone]
if '--write' in sys.argv: open(src+'reader.fx','w').write('\n'.join(lines))
print(len(dropped),'dropped:',' '.join(dropped))
