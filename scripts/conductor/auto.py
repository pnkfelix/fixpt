"""auto.py FILE:NAME:COMMENT ...: each FILE converted (`convert.py`) and
committed, a message from what the conversion found; stopping at the
first that fails, for a hand to take over."""
import sys, subprocess, re
import paths
X = paths.X
T = paths.T
ROOT = paths.ROOT
for spec in sys.argv[1:]:
    fname, name, comment = spec.split(':', 2)
    r = subprocess.run(['python3', X + 'convert.py', fname, name, comment], capture_output=True, text=True, cwd=ROOT, timeout=3500)
    out = r.stdout + r.stderr
    if r.returncode != 0:
        print('STOPPED at', fname); print(out[-2500:]); sys.exit(1)
    gives = re.search(r'conductor gives: (.*)', out).group(1).split()
    words = re.search(r'\| front end .*\|\s+([\d.]+) \|\s+\d+ \|\s*$', out, re.M)
    prev = subprocess.run(['git', 'log', '-1', '--format=%B'], capture_output=True, text=True, cwd=ROOT).stdout
    pm = re.search(r'Compiling the front end: ([\d.]+) M words', prev)
    entries = re.search(r"entries named: \[(.*?)\]", out).group(1)
    lines = [l for l in open(ROOT + '/crates/fixpt-fx26/src/' + fname).read().split('\n')]
    given = ', '.join('`%s`' % (g[:-len('-module')] if g.endswith('-module') else g) for g in gives)
    body = ('TODO.md §68, phase 2, a commit a file. `%s` (%s) is a `load-input`\n'
            'file, given %s, each typed by its signature. The conductor makes it first\n'
            'and gives it to the files made after it%s. %d lines.\n\n'
            'Compiling the front end: %s M words, from %s.\n') % (
        fname, comment.rstrip('.').lower(), given,
        ('; and names %s for Rust and `bootstrap.fx`' % entries.replace("'", '`')) if entries else '',
        len(lines) - 1, words.group(1) if words else '?', pm.group(1) if pm else '?')
    # The wrapped body.
    import textwrap
    paras = body.split('\n\n')
    body = '\n\n'.join(textwrap.fill(p.replace('\n', ' '), 72, break_on_hyphens=False, break_long_words=False) for p in paras) + '\n'
    open(T + 'body.txt', 'w').write(body)
    t = open(ROOT + '/TODO.md').read()
    m = re.search(r'- Checker converted \(a commit each\):.*?\.\n(?=- )', t, re.S)
    flat = ' '.join(l.strip() for l in m.group(0).strip().split('\n'))
    flat = flat.rstrip('.') + ', `%s`.' % fname
    block = textwrap.fill(flat, 72, subsequent_indent='  ', break_on_hyphens=False, break_long_words=False) + '\n'
    t = t[:m.start()] + block + t[m.end():]
    open(ROOT + '/TODO.md', 'w').write(t)
    c = subprocess.run(['sh', X + 'commit.sh', '%s made by the conductor, of the modules it uses' % fname, T + 'body.txt'],
                       capture_output=True, text=True, cwd=ROOT)
    print(fname, '->', c.stdout.strip(), '|', words.group(1) if words else '?', 'M words')
