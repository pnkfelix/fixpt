# Emacs: `fx26-mode`

Editing FX-26 in Emacs (30, with no packages beyond what it ships):
highlighting and indentation for `.fx` files, both of `fixpt`'s checkers
as you type, the type of the global at point, and a REPL that code is sent
to. Step 1 of PLAN's Q14; `fixpt lsp`, for `eglot`, is step 2.

## Setting it up

Build `fixpt` (`cargo build --release`), then in `~/.emacs.d/init.el`:

```elisp
(add-to-list 'load-path "~/Dev/Rust/fixpt/editors/emacs")
(require 'fx26-mode)
```

`fx26-mode` finds `fixpt` in `exec-path`, or else the release build in
this repository; `M-x customize-group RET fx26` sets another
(`fx26-program`) and the REPL's flags (`fx26-repl-arguments`; keep
`--emacs`).

## In a `.fx` buffer

| key                                   | what                                            |
| ------------------------------------- | ----------------------------------------------- |
| `C-M-x`, `C-c C-e`                    | send the top-level form at point to the REPL    |
| `C-c C-r`                             | send the region                                 |
| `C-c C-l`                             | save, and load the file into the REPL (`,load`) |
| `C-c C-z`                             | switch to the REPL, starting it if need be      |
| `M-x flymake-show-buffer-diagnostics` | every error the last check found                |

- **Checking as you type**: `flymake` pipes the buffer to `fixpt check -`
  (both checkers, about 0.3 s for a 370-line file) and underlines the
  subform each error is about. `fixpt` stops at a program's first error,
  so there is one at a time. If the checkers disagree, a warning on the
  first line says so; `fixpt check FILE` shows how.
- **The type at point**: on a global's name, the echo area shows its type
  and effect, as the last check that passed found them (`eldoc`).
- **Indentation** is the repository's: bodies two in, `define-rec` members
  and `tagcase` arms as definitions, arguments otherwise lined up as in
  Scheme, a comment alone on its line indented as code. Re-indenting the
  front end's 21,000 lines changes 3% of them, all where the source is
  itself irregular.

## The REPL

`M-x run-fx26` runs, in `*fx26*`, `fixpt --dialect fx26 --fx26-run
cellular --cellular-machine registers --calling-convention native --emacs
repl`: forms compiled to native code by register code; the code of what
you redefine is collected, so reloading on every save can go on all day
(300 reloads of a 370-line file, checked). `M-x fx26-restart-repl` starts
afresh. Without the three cellular flags (`fx26-repl-arguments`) the REPL
runs lowered Scheme, slower.
With `--emacs`, `fixpt` prints no continuation prompt, and takes `,at FILE
LINE COL` before a form: what is sent from a buffer is preceded by one, so
its errors name the file, line and column it came from, and
`compilation-shell-minor-mode` makes them links (`RET` or a click).

A redefinition at another type leaves what uses the name out of date,
keeping the old one, rather than running it again at once, so a reload
runs each form once: the REPL says what is out of date, `,list-outdated`
says why, and `,rerun-outdated` runs them again (`docs/fx26.md`,
"Redefinition").

What is not there yet (PLAN Q14, `TODO.md` §25): hover types for any
expression, not only globals, and completion, which wait for `fixpt lsp`;
`C-c C-c` stopping a running form, which waits for a fuel trap that
resumes (Q15).

## Tests

`editors/emacs/run-tests.sh`: indentation, highlighting, reading
`fixpt check`'s output, and, with `fixpt` built, `flymake` and the REPL
end to end.
