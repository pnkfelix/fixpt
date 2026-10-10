"""What the types files define: type and effect names (registry.json, kept
by extract.py, refreshed here from the files themselves) and datatype
constructors, each with its types file and how to load it."""
import re, os, json, glob
import paths
SRC = paths.SRC
D = os.path.dirname(os.path.abspath(__file__))
def loads():
    reg = json.load(open(D + '/registry.json'))
    out = {}
    for n, r in reg.items(): out[r['file']] = (r['var'], r['load'])
    return reg, out
def defined_in(path):
    t = re.sub(r';[^\n]*', '', open(path).read())
    types, effects, ctors = set(), set(), set()
    for m in re.finditer(r'^\(define-type (\S+)', t, re.M): types.add(m.group(1))
    for m in re.finditer(r'^\(define-effect (\S+)', t, re.M): effects.add(m.group(1))
    for m in re.finditer(r'^\(define-datatype \(?(\S+)', t, re.M):
        types.add(m.group(1))
        i = m.end(); d = 1 if t[m.start()+len('(define-datatype '):].startswith('(') else 0
        # constructors: groups at depth 1 of the datatype form
        j = m.start(); depth = 0; k = j
        while True:
            c = t[k]
            if c == '(':
                depth += 1
                if depth == 2:
                    nm = re.match(r'\(([^\s()]+)', t[k:]).group(1)
                    if t[k-1] != ' ' or True: ctors.add(nm)
            elif c == ')':
                depth -= 1
                if depth == 0: break
            k += 1
        ctors.discard(m.group(1))
    return types, effects, ctors
def table():
    """name -> (kind, types file, var, load)"""
    reg, ld = loads()
    out = {}
    for n, r in reg.items():
        out[n] = ('effect' if r['kind'] == 'effect' else 'type', r['file'], r['var'], r['load'])
    for f, (v, l) in ld.items():
        if not os.path.exists(SRC + f): continue
        ts, es, cs = defined_in(SRC + f)
        # Names the file defines itself that the registry missed: types
        # before constructors, a datatype's constructor often its name.
        for n in ts:
            if n not in out: out[n] = ('type', f, v, l)
        for n in es:
            if n not in out: out[n] = ('effect', f, v, l)
        for c in cs:
            if c not in out: out[c] = ('ctor', f, v, l)
    return out
def ctors():
    """constructor name -> (kind, types file, var, load): every one, a type
    of the same name being apart."""
    reg, ld = loads()
    out = {}
    for f, (v, l) in ld.items():
        if not os.path.exists(SRC + f): continue
        for c in defined_in(SRC + f)[2]:
            out.setdefault(c, ('ctor', f, v, l))
    return out
if __name__ == '__main__':
    t = table(); import collections
    print(collections.Counter(k for k, *_ in t.values()))
