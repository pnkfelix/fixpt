;;; The reader and the parser written in FX-26, made: `eager-reader.fx`,
;;; `parser.fx`, `parser-exps.fx` and `parser-top.fx` are module files of the
;;; reader's regions (`(module-parameters …)`), each loading the one before
;;; at its own, and are built in (`(load-module "fx26:…")`,
;;; `crate::built_in_module`). Here the last is made at the front end's
;;; regions, and the others reached through it; then what the rest of the
;;; front end uses of each is re-exported, as each file's own block was
;;; when it was one module of one program.
;;;
;;; What licenses running the reader on every keystroke (`licence.rs`) is
;;; its type: each entry point's effect is on the regions the reader is
;;; given and on no other, whichever they are, since the reader cannot name
;;; any other. So these may be any regions; they are the ones the rest of
;;; the front end names: `@s` its syntax, `@e` its prompt tag, `@m` its mark
;;; key, `@c` the lists it hands back, `@p` the parser's prompt tag.
;;;
;;; Unlike the files the conductor makes (`TODO.md` §68), what this names
;;; is at top level: Rust finds the reader's entry points, `make-reader`,
;;; and the parser's results' constructors there by name (`licence.rs`,
;;; `session.rs`, `syn.rs`), and `bootstrap.fx` and the conductor use them.
;;; So it names only what they use: the rest of each module stays inside.

(define make-reader (load-module "fx26:parser-top.fx"))
(define parser-top-module ((proj make-reader @s @e @m @c @p)))
(define parser-exps-module (with parser-top-module parser-exps-module))
(define parser-module (with parser-exps-module parser-module))
;; The eager reader, which the parser does not load (`syn.fx`).
(define make-eager-reader (load-module "fx26:eager-reader.fx"))
(define eager-reader-module ((proj make-eager-reader @s @e @m @c)))
;; From `eager-reader.fx`.
(import eager-reader-module waiting advance need fail entry eager-feed eager-feed-string
        eager-state-kind eager-state-position eager-state-message eager-state-data
        eager-state-syntax eager-context eager-status eager-hole-closers eager-start
        eager-start-fx26 read-text read-text-at atom lst dotted vec
        (type chars data syn syns state result word context closers)
        (effect marks parsing reads reading asks))
;; From `parser.fx`.
(import parser-module len drop label keep arity e-var e-int e-bool e-str e-char e-float e-sym e-unit
        e-lambda e-app e-plambda e-proj e-if e-letrec e-let e-begin e-prompt e-letregion e-rlambda
        e-the e-convention e-bloblet e-product e-extract e-sum e-tagcase e-module e-with t-define
        t-define-rec t-define-type t-define-effect t-define-convention t-define-syscall
        t-define-generative t-exp p-ok p-err quoted loaded loaded-files! includes-given!
        (type names exp top)
        (effect parses))
;; From `parser-top.fx`.
(define parse-program (with parser-top-module parse-program))
