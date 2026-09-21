#!/bin/sh
# Regenerate the checked-in conformance goldens from the GiffordHistory
# reference implementations.
#
# The goldens are committed, so the Rust test suite runs with no Racket
# installed and no archive checkout.  This script exists so that regenerating
# them is an explicit, reviewable diff rather than something that silently
# happens during a build.
#
#   FIXPT_GIFFORD   path to the GiffordHistory checkout
#                   (default: a sibling of this repository's parent)
#   RACKET          racket executable (default: whatever is on PATH)
set -eu

here=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
root=$(dirname "$here")
RACKET=${RACKET:-racket}

if ! command -v "$RACKET" >/dev/null 2>&1; then
    echo "regenerate: '$RACKET' not found; set RACKET to your racket binary" >&2
    echo "  e.g. RACKET='/Applications/Racket v9.3/bin/racket' $0" >&2
    exit 1
fi

echo "==> FX-91"
"$RACKET" "$here/fx91-golden.rkt" \
    "$root/tests/conformance/fx91/cases/tests.fx" \
    "$root/tests/conformance/fx91/tests.expected"

echo "==> FX-91 built-in module signature"
"$RACKET" "$here/fx91-stdmodule.rkt" \
    "$root/crates/fixpt-fx91/src/fx-module.fx"

echo "==> FX-87"
"$RACKET" "$here/fx87-golden.rkt" \
    "$root/tests/conformance/fx87/cases/kernel.fx" \
    "$root/tests/conformance/fx87/kernel.expected"

echo "==> FX-87 standard environment"
"$RACKET" "$here/fx87-stdenv.rkt" \
    "$root/crates/fixpt-fx87/src/standard.fx"

echo "done"
