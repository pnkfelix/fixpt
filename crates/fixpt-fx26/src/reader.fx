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
(define eager-reader-module (with parser-module eager-reader-module))
;; From `eager-reader.fx`.
(define-effect marks (select eager-reader-module marks))
(define-effect parsing (select eager-reader-module parsing))
(define-effect reads (select eager-reader-module reads))
(define-effect reading (select eager-reader-module reading))
(define-type chars (select eager-reader-module chars))
(define-type data (select eager-reader-module data))
(define-type syn (select eager-reader-module syn))
(define-type syns (select eager-reader-module syns))
(define-type state (select eager-reader-module state))
(define-type result (select eager-reader-module result))
(define-type word (select eager-reader-module word))
(define waiting (with eager-reader-module waiting))
(define advance (with eager-reader-module advance))
(define need (with eager-reader-module need))
(define fail (with eager-reader-module fail))
(define entry (with eager-reader-module entry))
(define eager-feed (with eager-reader-module eager-feed))
(define eager-feed-string (with eager-reader-module eager-feed-string))
(define eager-state-kind (with eager-reader-module eager-state-kind))
(define eager-state-position (with eager-reader-module eager-state-position))
(define eager-state-message (with eager-reader-module eager-state-message))
(define eager-state-data (with eager-reader-module eager-state-data))
(define eager-state-syntax (with eager-reader-module eager-state-syntax))
(define-type context (select eager-reader-module context))
(define-type closers (select eager-reader-module closers))
(define-effect asks (select eager-reader-module asks))
(define eager-context (with eager-reader-module eager-context))
(define eager-status (with eager-reader-module eager-status))
(define eager-hole-closers (with eager-reader-module eager-hole-closers))
(define eager-start (with eager-reader-module eager-start))
(define eager-start-fx26 (with eager-reader-module eager-start-fx26))
(define read-text (with eager-reader-module read-text))
(define atom (with eager-reader-module atom))
(define lst (with eager-reader-module lst))
(define dotted (with eager-reader-module dotted))
(define vec (with eager-reader-module vec))
;; From `parser.fx`.
(define-effect parses (select parser-module parses))
(define-type names (select parser-module names))
(define-type exp (select parser-module exp))
(define-type top (select parser-module top))
(define len (with parser-module len))
(define drop (with parser-module drop))
(define label (with parser-module label))
(define keep (with parser-module keep))
(define arity (with parser-module arity))
(define e-var (with parser-module e-var))
(define e-int (with parser-module e-int))
(define e-bool (with parser-module e-bool))
(define e-str (with parser-module e-str))
(define e-char (with parser-module e-char))
(define e-float (with parser-module e-float))
(define e-sym (with parser-module e-sym))
(define e-unit (with parser-module e-unit))
(define e-lambda (with parser-module e-lambda))
(define e-app (with parser-module e-app))
(define e-plambda (with parser-module e-plambda))
(define e-proj (with parser-module e-proj))
(define e-if (with parser-module e-if))
(define e-letrec (with parser-module e-letrec))
(define e-let (with parser-module e-let))
(define e-begin (with parser-module e-begin))
(define e-prompt (with parser-module e-prompt))
(define e-letregion (with parser-module e-letregion))
(define e-rlambda (with parser-module e-rlambda))
(define e-the (with parser-module e-the))
(define e-convention (with parser-module e-convention))
(define e-bloblet (with parser-module e-bloblet))
(define e-product (with parser-module e-product))
(define e-extract (with parser-module e-extract))
(define e-sum (with parser-module e-sum))
(define e-tagcase (with parser-module e-tagcase))
(define e-module (with parser-module e-module))
(define e-with (with parser-module e-with))
(define t-define (with parser-module t-define))
(define t-define-rec (with parser-module t-define-rec))
(define t-define-type (with parser-module t-define-type))
(define t-define-effect (with parser-module t-define-effect))
(define t-define-generative (with parser-module t-define-generative))
(define t-exp (with parser-module t-exp))
(define p-ok (with parser-module p-ok))
(define p-err (with parser-module p-err))
(define quoted (with parser-module quoted))
(define loaded (with parser-module loaded))
(define loaded-files! (with parser-module loaded-files!))
;; From `parser-top.fx`.
(define parse-program (with parser-top-module parse-program))
