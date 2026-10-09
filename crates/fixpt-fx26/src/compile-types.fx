;;; The types of `compile.fx`, its `compile-module`: a module file of no
;;; state, which it loads, and so may its clients (`TODO.md` §68); its
;;; items in the order they were there.

;; The types these use, from the files that define them.
(define parser-types ((proj (load-module "fx26:parser-types.fx") @s @e @m @c @p)))
(define-type exp (select parser-types exp))
(define-type names (select parser-types names))
(define-type syn (select parser-types syn))
(define-type syns-a (select parser-types syns-a))
(define check-env-types (load-module "fx26:check-env-types.fx"))
(define-type k-with-list (select check-env-types k-with-list))
(define table-types (load-module "fx26:table-types.fx"))
(define-type table (select table-types table))
;; What looking at the trees and the compiler's state may do: build lists
;; on @k (and, walking the trees, spin); and adding to code.
(define-effect c-builds (maxeff (read @globals) (read @k) (alloc @k)))
(define-effect c-walks (maxeff c-builds spin))
(define-effect c-emits (maxeff (read @globals) (read @k) (write @k) (alloc @k)))
;; What compiling may do: read the trees, build code on @k, and give up.
(define-effect compiles (maxeff c-emits (read @t) (goto @y)))
;; The parser's lists: a lambda's parameters, a `let`'s bindings (and a
;; product's fields, and a `tagcase`'s else), a `letrec`'s, a `tagcase`'s
;; arms, and expressions.
(define-type c-params (listof (productof (1 symbol) (2 syns-a)) acyclic))
(define-type c-binds (listof (productof (1 symbol) (2 exp)) acyclic))
(define-type c-recs (listof (productof (1 symbol) (2 syn) (3 exp)) acyclic))
(define-type c-cases (listof (productof (1 symbol) (2 bool) (3 names) (4 exp)) acyclic))
(define-type exps (listof exp acyclic))
;; A span of the program, by where it starts: where it ends, and what is
;; noted of it.
(define-type c-span (pairof int int @k))
(define-type c-spans (table int c-span @k))
;; A `letrec`-bound procedure lambda-lifted, as Twobit's pass 2 lifts
;; (`pass2p2.sch`): its closure, over nothing, made while compiling; the
;; names it would have captured, each passed as an argument before its own.
(define-type c-lift (productof (1 wcell) (2 (listof symbol acyclic))))
;; Whether a `letrec` is lifted: its members' indices in `c-lifts`, in a
;; list of one; none if not.
(define-type c-lifting (listof (listof int @k) @k))
;; Each expression's effect summary, by where it starts: where it ends, and
;; the summary, for each span starting there.
(define-type c-ends (listof c-span acyclic))
;; The same, by where each starts: a program's `with`s are many (a file's
;; re-exports), and each is asked for once (`TODO.md` §43).
(define-type c-with-table (table int k-with-list @k))
(define-type c-with-names (listof syms @k))
;;; ----------------------------------------------------------------- code

(define-datatype item
  (i-cell wcell)
  (i-label int)
  (i-branch int)
  (i-zbranch int))
(define-type items (listof item @k))
;; The code for one word so far, newest first.
(define-type code (ref items @k))
(define-datatype cresult (c-ok tword) (c-err string))
;; Where each label is, in cells, by label.
(define-type c-places (arrayof int @k))
;;; ------------------------------------------------------------ variables

(define-datatype loc
  (at-slot int)
  (at-free int)
  (at-global wglobal)
  ;; A `letrec` sibling not made yet, to be in this slot: a closure that
  ;; captures it holds a placeholder, patched once every sibling is made.
  (at-pending int)
  ;; A `letrec`-bound procedure, in its own body, where it is only called
  ;; in tail position: each call is a jump back to its start. (The int is
  ;; unused.)
  (at-loop int)
  ;; A `letrec`-bound procedure lambda-lifted (`c-lift`), by its index in
  ;; `c-lifts`: only called, by a closure over nothing made once, with the
  ;; names it would have captured passed first.
  (at-lifted int))
(define-type cenv (listof (pairof symbol loc @k) @k))
;; Where a name was found, in a list of one; none if it was not.
(define-type c-found (listof loc @k))
;; What register code knows of the procedure being compiled, when it is one
;; that knows itself: its name, where the name is, and its arity.
(define-type c-this (productof (1 symbol) (2 loc) (3 int) (4 int)))
;; The global environment as compiling has reached it: by name, a table of
;; each name's globals, newest first, each with its place in the order they
;; were made (`c-genv-count` so far). A body compiled where it was written
;; sees only the globals made before (an inlined body, a copy specialized at
;; a lambda): `c-genv`, the count of them; -1 when every global is seen.
(define-type c-globals-made (listof (pairof int loc @k) acyclic))
;;; ------------------------------------------------------------- free names
;;; The names a lambda's body uses that it does not bind: what its closure
;;; must carry, once globals and standard names are set aside.

(define-type syms (listof symbol acyclic))
;; Each `letrec` in tail position asked about: which bindings are join points
;; (`regcode.fx`'s `r-join-flags`), by where its body starts: where the body
;; ends, the names bound, and the answer. Asked of the same `letrec` many
;; times over (each time what encloses it is asked whether it calls), and
;; the answer is the same each time.
(define-type c-join-answer (productof (1 int) (2 syms) (3 (listof bool acyclic))))
;; Each standard operation's word as a value, made once (step 4): the
;; stack code's, which register code uses too.
(define-type c-standard-word (productof (1 string) (2 tword)))
;; The specialized copies made (`c-make-copy`), by the lambda's span
;; (`c-span-key`): each the procedure's word, what the lambda captures, the
;; globals it sees, and the copy's word and what that captures.
(define-type c-spec-copy (productof (1 tword) (2 syms) (3 int) (4 tword) (5 syms)))
(define-type c-spec-copies (listof c-spec-copy @k))
;; `letrec`: every binding is a lambda (the checker says so). Each closure
;; is made in its slot, with a placeholder for a sibling not made yet; then
;; each placeholder is patched with its sibling. Nothing runs in between, so
;; no one sees the knot tied. A name used only in calls of itself that are
;; loops is not captured at all.
(define-type patches (listof (pairof int int @k) @k))

;;; ------------------------------------------------------------ signatures

;; What its clients use of it (`compile-programs.fx`).
;; The types it names, from the files that define them.
(define-type k-facts (select check-env-types k-facts))
;; The types it names, from the files that define them.
(define check-types-types (load-module "fx26:check-types-types.fx"))
(define-type k-ids (select check-types-types k-ids))
(define-type compile-sig
  (moduleof (val c-frozen-define-at
                 (subr (maxeff (read @globals) (read @k)) (int int) bool))
            (val c-tag
                 (prompt-tag cresult
                             cresult
                             (maxeff (alloc @k)
                                     (read @globals)
                                     (read @k)
                                     (read @t)
                                     (write @k)
                                     spin)
                             @y))
            (val c-op
                 (subr (maxeff (alloc @k) (read @globals) (read @k) (write @k))
                       (code int)
                       unit))
            (val c-op1
                 (subr (maxeff (alloc @k) (read @globals) (read @k) (write @k))
                       (code int wcell)
                       unit))
            (val c-lit
                 (subr (maxeff (alloc @k) (read @globals) (read @k) (write @k))
                       (code wcell)
                       unit))
            (val c-assemble
                 (subr (maxeff (alloc @k) (read @globals) (read @k) (write @k) spin)
                       (code symbol)
                       tword))
            (val c-this-params (ref int @k))
            (val c-genv-index
                 (ref (bloblet (fields (subr pure (symbol) int)
                                       (subr pure (symbol symbol) bool)
                                       (arrayof (listof (pairof symbol c-globals-made @k)
                                                        acyclic)
                                                @k)
                                       int)
                               @k)
                      @k))
            (val c-genv-count (ref int @k))
            (val c-genv (ref int @k))
            (val c-global-find
                 (subr (maxeff (alloc @k) (read @globals) (read @k)) (symbol int) c-found))
            (val c-genv-push!
                 (subr (maxeff (alloc @k) (read @globals) (read @k) (write @k))
                       (symbol int wglobal)
                       unit))
            (val c-where
                 (subr (maxeff (alloc @k) (read @globals) (read @k) spin)
                       (cenv symbol)
                       c-found))
            (val c-set-facts!
                 (subr (maxeff (alloc @k) (read @globals) (read @k) (read @t) (write @k))
                       (k-facts)
                       unit))
            (val c-lambda-of
                 (subr (maxeff (alloc @k) (read @globals)) (exp) (listof exp @k)))
            (val c-mentions?
                 (subr (maxeff (alloc @k) (read @globals) (read @k) spin) (exp symbol) bool))
            (val c-plain-table (ref c-spans @k))
            (val c-plain-fx-at (subr (maxeff (read @globals) (read @k)) (int int) bool))
            (val c-field-at
                 (subr (maxeff (alloc @k) (read @globals) (read @k)) (int int) int))
            (val c-genv-now
                 (subr (maxeff (read (globals c-genv c-genv-count)) (read @k)) () int))
            (val c-count-exps (subr (read @globals) (exps) int))
            (val c-count-params (subr (read @globals) (c-params) int))
            (val c-registers (ref bool @k))
            (val c-summary-at (subr (maxeff (read @globals) (read @k)) (int int) int))
            (val c-conversion-at (subr (maxeff (read @globals) (read @k)) (exp) int))
            (val c-apply-shares-at (subr (maxeff (read @globals) (read @k)) (int int) bool))
            (val c-with-at
                 (subr (maxeff (alloc @k) (read @globals) (read @k)) (int int) c-with-names))
            (val c-with-places-at
                 (subr (maxeff (alloc @k) (read @globals) (read @k))
                       (int int)
                       (listof k-ids @k)))
            (val c-reshape-at
                 (subr (maxeff (alloc @k) (read @globals) (read @k))
                       (exp)
                       (listof k-ids @k)))
            (val c-applied-let
                 (subr (maxeff (alloc @k) (read @globals) (read @k) spin)
                       (exp exps)
                       (listof (productof (1 c-binds) (2 exp)) @k)))
            (val c-length (subr (maxeff (read @globals) (read @k) spin) (syms) int))
            (val c-loops-only
                 (subr (maxeff (alloc @k) (read @globals) (read @k) spin)
                       (exp symbol int bool)
                       bool))))
