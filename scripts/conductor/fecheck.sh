#!/bin/sh
# fecheck.sh: rebuild, then check the front end (both checkers); print the verdict.
X=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$X/../.." && pwd)
T=${CONDUCTOR_TMP:-$ROOT/target/conductor}
mkdir -p "$T"
cd "$ROOT"
"$X/t" 900 cargo build --release --offline 2>&1 | grep -E '^error' -A5
target/release/fixpt front-end-files 2>&1 | grep -v 'module file' | awk '{print $2}' | xargs cat > "$T/fe-all.fx"
"$X/t" 300 target/release/fixpt --dialect fx26 check "$T/fe-all.fx" > "$T/fe-check.txt" 2>&1
grep -E '^(Rust|FX-26): +!|^!|agree|^fixpt|killed after' "$T/fe-check.txt" | cut -c1-300 | head -6
