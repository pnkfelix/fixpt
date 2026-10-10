"""deps.py FILE: the top-level names of other front-end files that FILE uses,
grouped by the file defining them (the last definer before FILE)."""
import sys, re, subprocess, collections
import paths
ROOT=paths.ROOT
files=[l.split()[1] for l in subprocess.run([ROOT+'/target/release/fixpt','front-end-files'],capture_output=True,text=True).stdout.splitlines() if 'module file' not in l and l.strip()]
# And what Rust calls by name: the front end's entry points.
RUST=open(ROOT+'/crates/fixpt-fx26/src/session.rs').read()
TOK=re.compile(r"[A-Za-z0-9!$%&*/:<=>?^_~+.@|-]+")
def strip(t):
    """`t` without comments, strings' contents and characters: one pass,
    as the reader reads them."""
    out = []; i = 0; n = len(t)
    while i < n:
        c = t[i]
        if c == ';':
            j = t.find('\n', i); i = n if j < 0 else j; continue
        if c == '#' and t.startswith('#\\', i):
            j = i + 3
            while j < n and t[j] not in ' \n\t()': j += 1
            i = j; out.append(' '); continue
        if c == '"':
            j = i + 1
            while j < n and t[j] != '"':
                j += 2 if t[j] == '\\' else 1
            out.append('""'); i = j + 1; continue
        out.append(c); i += 1
    return ''.join(out)
def toplevel_names(t):
    t=strip(t); out=[]; d=0; i=0
    # names defined at depth 1 (top-level forms)
    for m in re.finditer(r'[()]|[^\s()]+',t):
        s=m.group()
        if s=='(': d+=1; continue
        if s==')': d-=1; continue
    for m in re.finditer(r'^\((define\*?|define-type|define-effect|define-datatype|define-generative)\s+\(?([^\s()]+)',t,re.M):
        out.append(m.group(2))
    # A datatype's constructors: the heads of the groups at its depth 1.
    for m in re.finditer(r'^\(define-datatype ', t, re.M):
        i = m.start(); d = 0; first = t[m.end()] == '('
        while True:
            c = t[i]
            if c == '(':
                d += 1
                if d == 2:
                    h = re.match(r'\(([^\s()]+)', t[i:])
                    if h and not first: out.append(h.group(1))
                    first = False
            elif c == ')':
                d -= 1
                if d == 0: break
            i += 1
    return out
target=sys.argv[1]
src={f:open(f).read() for f in files}
tf=[f for f in files if f.endswith('/'+target)][0]
idx=files.index(tf)
definer={}
for f in files[:idx]:
    for n in toplevel_names(src[f]): definer[n]=f
own=set(toplevel_names(src[tf]))
used=set(TOK.findall(strip(src[tf])))
by=collections.defaultdict(list)
for n in sorted(used):
    if n in definer and n not in own: by[definer[n].split('/')[-1]].append(n)
for f,ns in by.items(): print(f, len(ns), ' '.join(ns))
users=[g.split('/')[-1] for g in files[idx+1:] if set(TOK.findall(strip(src[g]))) & set(n for n in own)]
print('-- later files using its names:', ' '.join(users))
print('-- Rust entry points among them:', ' '.join(n for n in sorted(own) if '"%s"' % n in RUST))
