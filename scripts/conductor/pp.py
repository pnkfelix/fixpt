"""Lay an S-expression out within a width: a list that fits stays on one
line; else its head and first element, then each other element on a line
of its own under the first."""
import re
def parse(s):
    toks = re.findall(r'\(|\)|[^\s()]+', s); i = 0
    def rd():
        nonlocal i
        t = toks[i]; i += 1
        if t == '(':
            out = []
            while toks[i] != ')': out.append(rd())
            i += 1; return out
        return t
    return rd()
def flat(x): return x if isinstance(x, str) else '(' + ' '.join(flat(y) for y in x) + ')'
def lay(x, col, width):
    f = flat(x)
    if isinstance(x, str) or col + len(f) <= width or len(x) == 0: return f
    if len(x) == 1: return '(' + lay(x[0], col + 1, width) + ')'
    head = flat(x[0])
    if isinstance(x[0], str) and len(x) > 2:
        c = col + 1 + len(head) + 1
        first = lay(x[1], c, width)
        rest = [lay(y, c, width) for y in x[2:]]
        return '(' + head + ' ' + first + ''.join('\n' + ' ' * c + r for r in rest) + ')'
    c = col + 1
    parts = [lay(y, c, width) for y in x]
    return '(' + parts[0] + ''.join('\n' + ' ' * c + p for p in parts[1:]) + ')'
def layout(s, col, width=92): return lay(parse(s), col, width)
