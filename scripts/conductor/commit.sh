#!/bin/sh
# commit.sh SUBJECT BODY-FILE: commit everything tracked or new under the
# front end's sources and tests and TODO.md; the message the subject, the
# body, the fresh bench tables ($T/bench-new.txt, written by convert.py),
# and $T/trailer.txt (attribution lines, say) if there is one.
X=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$X/../.." && pwd)
T=${CONDUCTOR_TMP:-$ROOT/target/conductor}
cd "$ROOT"
{ echo "$1"; echo; cat "$2"; echo; cat "$T/bench-new.txt"; if [ -f "$T/trailer.txt" ]; then echo; cat "$T/trailer.txt"; fi; } > "$T/msg.txt"
git add TODO.md crates/fixpt-fx26/src crates/fixpt-fx26/tests && git commit -q -F "$T/msg.txt" && git log --oneline -1 | cat
