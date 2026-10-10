"""convert.py FILE NAME COMMENT: the whole conversion of FILE, stopping at
the first failure: a fresh check, the conversion, lib.rs, the conductor
(NAME made first, COMMENT above it; its Rust and bootstrap entry points
named), the check again, the suite, the bench tables."""
import sys, subprocess, re
import paths
X = paths.X
T = paths.T
ROOT = paths.ROOT
fname, name, comment = sys.argv[1:4]
def run(cmd, timeout=1800):
    r = subprocess.run(cmd, shell=True, capture_output=True, text=True, cwd=ROOT, timeout=timeout)
    return r.stdout + r.stderr
def check():
    o = run('sh %sfecheck.sh' % X)
    if 'both checkers agree' not in o: sys.exit('check failed:\n' + o[-1500:])
check()
deps = run('python3 %sdeps.py %s' % (X, fname))
entries = re.search(r'-- Rust entry points among them: (.*)', deps).group(1).split()
later = re.search(r'-- later files using its names: (.*)', deps).group(1).split()
boot = open(ROOT + '/crates/fixpt-fx26/src/bootstrap.fx').read()
own = open(ROOT + '/crates/fixpt-fx26/src/' + fname).read()
exported = re.findall(r'^\(define (\S+) \(with \S+-module \S+\)\)', own, re.M)
entries += [n for n in exported if re.search(r'[\s(]%s[\s)]' % re.escape(n), boot) and n not in entries]
o = run('python3 %sto_input3.py %s' % (X, fname)); print(o.strip())
gives = re.search(r'conductor gives: (.*)', o)
if not gives: sys.exit('conversion failed')
old = re.search(r'^\(define (\S+)\s+\(module', own, re.M).group(1)
print(run('python3 %slib_move.py %s' % (X, fname)).strip())
subprocess.run(['python3', X + 'conductor_add.py', name, fname, comment, old] + gives.group(1).split(), cwd=ROOT, capture_output=True)
if entries: print(run('python3 %sconductor_export.py %s %s' % (X, name, ' '.join(entries)))[-300:])
print('entries named:', entries, '; later users:', later)
long = run("awk 'length > 100 {print FILENAME\": \"FNR\": \"length}' crates/fixpt-fx26/src/*.fx | grep -v layout.fx")
if long.strip(): print('LONG LINES:\n' + long)
check(); print('both checkers agree')
o = run(paths.TIMEOUT + ' 900 cargo test --release --offline --no-fail-fast 2>&1 | grep -E "^test result|FAILED|panicked|^error|could not compile|killed after"', 1000)
# A build that fails runs no tests, and says no `FAILED`: so that, and too few
# results, fail too.
fails = [l for l in o.splitlines() if 'FAILED' in l or 'panicked' in l or l.startswith('error') or 'could not compile' in l or 'killed after' in l]
if o.count('test result: ok') < 100: fails.append('only %d test results ok' % o.count('test result: ok'))
if fails: sys.exit('suite failed:\n' + '\n'.join(fails))
print('suite passes')
print(run(paths.TIMEOUT + " 900 target/release/fixpt bench --front-end --tables compile 2>/dev/null | grep 'front end'"))
run(paths.TIMEOUT + " 900 target/release/fixpt bench 2>/dev/null | sed -n '/^| program/,$p' > %sbench-new.txt" % T)
print(run('git status --short | grep -v "^??"; git status --short crates | grep "^??"'))
