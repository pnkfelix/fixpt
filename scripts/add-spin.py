#!/usr/bin/env python3
"""Add `spin` to each effect that reads `@globals` without it, in FX-26
files: what reading any global says since the first definition's exemption
was dropped (2026-10-31; `docs/fx26.md`, "Globals as a region").

A `(maxeff ...)` with `(read @globals)` among its parts and no `spin` gets
` spin` after that part; a `(read @globals)` that is a whole effect
becomes `(maxeff (read @globals) spin)`. Comments, strings and character
literals are left alone. Each file is rewritten in place; the files changed
and how many edits each are printed.

    scripts/add-spin.py FILE.fx ...
"""
import sys

READ = "(read @globals)"


def lists(text):
    """Each parenthesised list outside comments, strings and characters:
    (start, end, parent's start or None), `end` the index of its `)`."""
    out, stack, i, n = [], [], 0, len(text)
    while i < n:
        c = text[i]
        if c == ";":
            while i < n and text[i] != "\n":
                i += 1
            continue
        if c == '"':
            i += 1
            while i < n and text[i] != '"':
                i += 2 if text[i] == "\\" else 1
            i += 1
            continue
        if text.startswith("#\\", i):
            i += 3
            while i < n and text[i].isalnum():
                i += 1
            continue
        if text.startswith("#|", i):
            j = text.find("|#", i + 2)
            i = n if j < 0 else j + 2
            continue
        if c == "(":
            stack.append(i)
        elif c == ")" and stack:
            s = stack.pop()
            out.append((s, i, stack[-1] if stack else None))
        i += 1
    return out


def says_spin(text, start, end):
    """Whether the list at `start` has `spin` among its own parts."""
    depth = 0
    for k in range(start + 1, end):
        c = text[k]
        if c == "(":
            depth += 1
        elif c == ")":
            depth -= 1
        elif depth == 0 and text.startswith("spin", k):
            before, after = text[k - 1], text[k + 4] if k + 4 < len(text) else " "
            if (before.isspace() or before == "(") and (after.isspace() or after == ")"):
                return True
    return False


def fix(text):
    ls = lists(text)
    end_of = {s: e for s, e, _ in ls}
    edits, spun = [], set()
    for s, e, parent in ls:
        if text[s:e + 1] != READ:
            continue
        if parent is not None and text.startswith("(maxeff", parent) and text[parent + 7] in " \n\t":
            if parent not in spun and not says_spin(text, parent, end_of[parent]):
                spun.add(parent)
                edits.append((e + 1, 0, " spin"))
        else:
            edits.append((s, e + 1 - s, "(maxeff (read @globals) spin)"))
    for pos, length, new in sorted(edits, reverse=True):
        text = text[:pos] + new + text[pos + length:]
    return text, len(edits)


def main(paths):
    for path in paths:
        with open(path) as f:
            text = f.read()
        fixed, count = fix(text)
        if count:
            with open(path, "w") as f:
                f.write(fixed)
            print(count, path)


if __name__ == "__main__":
    main(sys.argv[1:])
