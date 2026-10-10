import sys,re
def sexp_end(s,i):
    # i at '(' ; return index after matching ')', skipping strings, chars, comments
    d=0; j=i
    while j<len(s):
        c=s[j]
        if c=='"':
            j+=1
            while s[j]!='"':
                if s[j]=='\\': j+=1
                j+=1
        elif c==';':
            while j<len(s) and s[j]!='\n': j+=1
            continue
        elif c=='#' and s[j+1]=='\\': j+=3; continue
        elif c=='(': d+=1
        elif c==')':
            d-=1
            if d==0: return j+1
        j+=1
    return -1
def candidates(s):
    out=[]
    for m in re.finditer(r'\(the\s',s):
        i=m.start()
        # skip in comments
        ls=s.rfind('\n',0,i)+1
        if ';' in s[ls:i]: continue
        e=sexp_end(s,i)
        inner=s[i+5:e-1].lstrip()
        # type: atom or sexp
        if inner.startswith('('):
            te=sexp_end(inner,0); T=inner[:te]
        else:
            te=re.match(r'\S+',inner).end(); T=inner[:te]
        body=inner[te:].strip()
        if '@' in T: continue
        if not body.startswith('('): continue
        head=re.match(r'\(\s*([^\s()]+)',body)
        if not head or head.group(1) in ('lambda','new','make-array','cons','list','product','sum','make-bloblet','letrec','let','let*','begin','if','cond','case','tagcase','typecase','plambda','vlambda','rlambda','prompt','the'): continue
        out.append((i,e,T,body))
    return out
if __name__=='__main__':
    tot=0
    for f in sys.argv[1:]:
        c=candidates(open(f).read()); tot+=len(c)
        if c: print(len(c), f)
    print('total',tot)
