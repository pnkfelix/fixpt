#!/usr/bin/env python3
"""Sum the files `FIXPT_PHASE_TIMES=dir` leaves (`TODO.md` §252,
`fixpt_memmgmt::phases`): one per process, each path of phases with its
exclusive nanoseconds, entries, collections begun and words they copied.

    FIXPT_PHASE_TIMES=/tmp/pt cargo nextest run --workspace
    scripts/phase-times.py /tmp/pt [--tests N] [--paths N]

Says how the files were written (at exit, a snapshot, a signal), then the
time by innermost phase, by work (a path's first `fx:` entry if it has one,
else its innermost phase), the collections by the phase that began them,
and the most costly test binaries and tests.
"""
import collections
import glob
import os
import sys


def read(path):
    head, rows = {}, []
    with open(path) as f:
        for line in f:
            line = line.rstrip("\n")
            if line.startswith("# "):
                k, _, v = line[2:].partition("\t")
                head[k] = v
                continue
            parts = line.split("\t")
            if len(parts) == 5:
                rows.append((parts[0], *map(int, parts[1:])))
    return head, rows


def test_of(args):
    """A process's binary and test, from its arguments: nextest runs a test
    binary as `BIN --exact NAME …`; anything else (a `fixpt` a test runs)
    is its command."""
    words = args.split()
    if not words:
        return ("?", "?")
    binary = os.path.basename(words[0])
    if "--exact" in words:
        i = words.index("--exact")
        name = words[i + 1] if i + 1 < len(words) else "?"
        return (binary.rsplit("-", 1)[0], name)
    return (binary, " ".join(words[1:3]))


def work(path):
    phases = path.split(";")
    for p in phases:
        if p.startswith("fx:"):
            return p
    return phases[-1]


def show(title, counter, total, n):
    print(f"\n{title}")
    for k, v in counter.most_common(n):
        print(f"  {v / 1e9:10.3f} s  {100 * v / max(total, 1):5.1f}%  {k}")


def main():
    args = sys.argv[1:]
    if not args:
        sys.exit(__doc__)
    dir_ = args[0]
    tests_n = int(args[args.index("--tests") + 1]) if "--tests" in args else 15
    paths_n = int(args[args.index("--paths") + 1]) if "--paths" in args else 0
    how = collections.Counter()
    leaf, by_work, by_path = collections.Counter(), collections.Counter(), collections.Counter()
    gcs, copied = collections.Counter(), collections.Counter()
    per_binary, per_test = collections.Counter(), collections.Counter()
    unread = 0
    for path in glob.glob(os.path.join(dir_, "*.tsv")):
        head, rows = read(path)
        how[head.get("fixpt phase times", "?").split(" ")[0]] += 1
        unread += int(head.get("threads not read", 0))
        binary, test = test_of(head.get("args", ""))
        for p, nanos, _entries, cols, words in rows:
            leaf[p.split(";")[-1]] += nanos
            by_work[work(p)] += nanos
            by_path[p] += nanos
            if cols:
                gcs[p.split(";")[-1]] += cols
                copied[p.split(";")[-1]] += words
            per_binary[binary] += nanos
            per_test[f"{binary} {test}"] += nanos
    total = sum(leaf.values())
    spawned = sum(v for k, v in per_binary.items() if k == "fixpt")
    print(f"{sum(how.values())} processes: " + ", ".join(f"{n} by {k}" for k, n in how.most_common()))
    if how.get("snapshot"):
        print("  (a snapshot: the process did not reach its exit, its times up to a second short)")
    if unread:
        print(f"  {unread} threads not read")
    print(f"{total / 1e9:.3f} s in all")
    if spawned:
        print(f"  of which {spawned / 1e9:.3f} s in `fixpt` processes tests ran, whose waits "
              "for them their tests' `other` counts again")
    show("By innermost phase:", leaf, total, 25)
    show("By work (a path's first `fx:` entry, else its innermost phase):", by_work, total, 25)
    print("\nCollections, by the phase that began them:")
    for k, n in gcs.most_common(15):
        print(f"  {n:8d}  {copied[k] / 1e6:10.1f} M words copied  {k}")
    show("Test binaries:", per_binary, total, tests_n)
    show("Tests:", per_test, total, tests_n)
    if paths_n:
        show("Paths:", by_path, total, paths_n)


if __name__ == "__main__":
    main()
