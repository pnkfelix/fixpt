"""extract.py FILE MODULE TYPES: move the type items of top-level module
MODULE in front-end FILE into module file TYPES (fx26:TYPES), importing the
types they use from the types files in registry.json; the module loads
TYPES and names what it defined. Prints what it did; refuses items it
cannot move (a type that selects from a module value)."""
import sys,os,re,json
D=os.path.dirname(os.path.abspath(__file__))
SRC='crates/fixpt-fx26/src/'
sys.path.insert(0,os.path.dirname(D))
from thes import sexp_end
TOK=re.compile(r"[A-Za-z0-9!$%&*/:<=>?^_~+.@-]+")
def items(body,base):
    """(comment_start, item_start, item_end) of each depth-1 form in body"""
    out=[]; i=0; cstart=None
    while i<len(body):
        c=body[i]
        if c in ' \t\n': i+=1; continue
        if c==';':
            if cstart is None: cstart=i
            while i<len(body) and body[i]!='\n': i+=1
            continue
        if c=='(':
            e=sexp_end(body,i); out.append((base+(cstart if cstart is not None else i),base+i,base+e)); i=e; cstart=None; continue
        if c==')': break
        i+=1
    return out
def head(s):
    m=re.match(r'\(\s*([^\s()]+)\s+\(?([^\s()]+)',s); return m.groups() if m else (None,None)
def ctors(item):
    # variants of a define-datatype: depth-1 groups after the name
    m=re.match(r'\(define-datatype\s+\(?[^\s()]+(\s+\([^()]*\))*\)?',item)
    body=item[item.index(head(item)[1])+len(head(item)[1]):]
    if head(item)[1] and item[len('(define-datatype'):].lstrip().startswith('('):
        e=sexp_end(item, item.index('(',1)); body=item[e:]
    names=[]; d=0; i=0
    while i<len(body):
        c=body[i]
        if c==';':
            while i<len(body) and body[i]!='\n': i+=1
            continue
        if c=='(':
            if d==0: names.append(re.match(r'\(([^\s()]+)',body[i:]).group(1))
            d+=1
        elif c==')': d-=1
        i+=1
    return names
def main(file,mod,types):
    reg=json.load(open(D+'/registry.json'))
    existing = open(SRC+types).read() if os.path.exists(SRC+types) else None
    p=SRC+file; s=open(p).read()
    k=s.index(f'(define {mod} (module'); m0=s.index('(module',k); m1=sexp_end(s,m0)
    body_start=m0+len('(module')
    its=items(s[body_start:m1-1],body_start)
    tys=[]; 
    for (cs,st,en) in its:
        h,n=head(s[st:en])
        if h in ('define-type','define-datatype','define-effect'):
            if re.search(r'\((select|with)\s',re.sub(r';[^\n]*','',s[st:en])): sys.exit(f'refuse: {n} selects from a module: {s[st:en][:80]}')
            tys.append((cs,st,en,h,n))
    if not tys: sys.exit('no types')
    defined=set(n for *_,n in tys)
    def dedent(t):
        ls=t.split('\n'); ind=min((len(l)-len(l.lstrip()) for l in ls[1:] if l.strip()),default=0)
        first_ind=len(ls[0])-len(ls[0].lstrip())
        return '\n'.join(l[ind:] if l[:ind].strip()=='' else l for l in ls)
    blocks=[]
    for (cs,st,en,h,n) in tys:
        pre=s[cs:st]; it=s[st:en]
        lead=re.match(r'[ \t]*',s[s.rfind('\n',0,cs)+1:cs]).group(0) if cs>0 else ''
        txt=(s[s.rfind('\n',0,cs)+1:en])
        lines=txt.split('\n'); ind=len(lines[0])-len(lines[0].lstrip())
        blocks.append('\n'.join(l[ind:] if l[:ind].strip()=='' else l for l in lines))
    ttext='\n'.join(blocks)
    toks=set(TOK.findall(re.sub(r';[^\n]*','',ttext)))
    need={}
    for t in sorted(toks):
        if t in defined or t not in reg: continue
        need.setdefault(reg[t]['file'],[]).append(t)
    imp=[]
    for f,names in need.items():
        r=reg[names[0]]; v=r['var']
        imp.append(f"(define {v} {r['load']})")
        for n in names:
            kw='define-effect' if reg[n]['kind']=='effect' else 'define-type'
            imp.append(f"({kw} {n} (select {v} {n}))")
    tv=types.replace('.fx','')
    out=[f";;; The types of `{file}`, its `{mod}`: a module file of no",
         ";;; state, which it loads, and so may its clients (`TODO.md` §68); its",
         ";;; items in the order they were there.",""]
    if imp: out+=[";; The types these use, from the files that define them."]+imp+[""]
    if existing is None:
        open(SRC+types,'w').write('\n'.join(out)+ttext.strip()+'\n')
    else:
        # Into the file there, before its signatures.
        block=('\n'.join([";; The types these use, from the files that define them."]+imp)+'\n' if imp else '')+ttext.strip()+'\n'
        mark=';;; ------------------------------------------------------------ signatures'
        k=existing.find(mark)
        new=(existing[:k]+block+'\n'+existing[k:]) if k>=0 else existing.rstrip('\n')+'\n\n'+block
        new=new.replace(f";;; The signature of `{file}`, its `{mod}`,\n;;; as its clients use it (`TODO.md` §68): a module file of no state.",
                        f";;; The types of `{file}`, its `{mod}`, and its signature as its\n;;; clients use it (`TODO.md` §68): a module file of no state.")
        open(SRC+types,'w').write(new)
    # module imports
    mi=[]
    for (cs,st,en,h,n) in tys:
        kw='define-effect' if h=='define-effect' else 'define-type'
        mi.append(f"({kw} {n} (select {tv} {n}))")
        if h=='define-datatype':
            for c in ctors(s[st:en]): mi.append(f"(define {c} (with {tv} {c}))")
    # cut type items from module (from end), insert imports at body start
    for (cs,st,en,h,n) in reversed(tys):
        a=s.rfind('\n',0,cs)+1; b=en
        if s[b:b+1]=='\n': b+=1
        s=s[:a]+s[b:]
    k=s.index(f'(define {mod} (module'); ins=s.index('(module',k)+len('(module')
    s=s[:ins]+'\n'+'\n'.join(mi)+'\n'+s[ins:]
    # The types file loaded before the module, so that it is not among its
    # values; the module names what it uses of it.
    pre=(f";; Its types (`{types}`), loaded before the module so that they are\n"
         f";; not among its values; the module names what it uses of them.\n"
         f"(define {tv} (load-module \"fx26:{types}\"))\n")
    s=s[:k]+pre+s[k:]
    open(p,'w').write(s)
    for (cs,st,en,h,n) in tys:
        reg[n]={'file':types,'var':tv,'load':f'(load-module "fx26:{types}")','kind':'effect' if h=='define-effect' else 'type'}
    json.dump(reg,open(D+'/registry.json','w'),indent=0)
    # registered as a module file built in
    L=SRC+'lib.rs'; t=open(L).read()
    if f'"{types}"' in t:
        print(f'{len(tys)} types to {types} (there already); imports from', {f:len(v) for f,v in need.items()}); return
    m=re.search(r'pub const FRONT_END_MODULES: \[\(&str, &str\); (\d+)\] = \[',t)
    t=t.replace(m.group(0),m.group(0).replace(m.group(1),str(int(m.group(1))+1)))
    const=tv.upper().replace('-','_')
    t=t.replace('    ("table-types.fx", TABLE_TYPES),\n',f'    ("table-types.fx", TABLE_TYPES),\n    ("{types}", {const}),\n',1)
    k=t.index("/// Hash tables' types: a module file of no state")
    t=t[:k]+f"/// The types of `{file}`: a module file of no state (`TODO.md` §68).\npub const {const}: &str = include_str!(\"{types}\");\n\n"+t[k:]
    open(L,'w').write(t)
    print(f'{len(tys)} types to {types}; imports from', {f:len(v) for f,v in need.items()})
if __name__=='__main__': main(*sys.argv[1:4])
