#!/bin/sh
# fx26-mode's tests, in a batch Emacs. Those that run fixpt need it built
# (cargo build --release) and are skipped otherwise.
cd "$(dirname "$0")" || exit 1
exec emacs --batch -Q -L . -L test -l test/fx26-mode-tests.el -f ert-run-tests-batch-and-exit
