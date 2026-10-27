;;; The signature of `check-read-descs.fx`, its `check-read-descs-module`,
;;; as its clients use it (`TODO.md` §68): a module file of no state.

;;; ------------------------------------------------------------ signatures

;; What its clients use of it (`check-program.fx`).
;; The types it names, from the files that define them.
(hide (define check-types-types (load-module "fx26:check-types-types.fx")))
(define-type k-eff (select check-types-types k-eff))
(hide (define parser-types ((proj (load-module "fx26:parser-types.fx") @s @e @m @c @p))))
(define-type syn (select parser-types syn))
(define-type top (select parser-types top))
(define-type k-tops (listof top acyclic))
(define-type k-out (listof string acyclic))
;; The types it names, from the files that define them.
(import check-types-types (type k-binders k-descs k-parts k-names))
;; The types it names, from the files that define them.
(define-type k-ids (select check-types-types k-ids))
;; The types it names, from the files that define them.
(hide (define check-env-types (load-module "fx26:check-env-types.fx")))
(define-type k-selects (select check-env-types k-selects))
;; The types it names, from the files that define them.
(hide (define check-read-types (load-module "fx26:check-read-types.fx")))
(define-type k-syns (select check-read-types k-syns))
;; The types it names, from the files that define them.
(define-type k-desc (select check-types-types k-desc))
(define-type check-read-descs-sig
  (moduleof (val k-parse-effect
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (syn)
                       k-eff))
            (val k-parse-type
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (syn)
                       int))
            (val k-written-arrow-star? (subr (maxeff (read @globals) (read @s) spin) (syn) bool))
            (val k-define-type
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read
                                (globals ds-rec
                                         k-ahead-filled
                                         k-ahead-take
                                         k-grounded
                                         k-note-closed
                                         k-push-desc
                                         k-set-link
                                         k-slot))
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (symbol syn int int)
                       int))
            (val k-parse-fun
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (syn int)
                       int))
            (val k-selects-in
                 (subr (maxeff (alloc @t) (read @globals) (read @t) (write @t) spin)
                       (int)
                       k-selects))
            (val k-parse-types
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (k-syns)
                       k-ids))
            (val k-parse-d
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (syn)
                       k-desc))
            (val k-read-in-order?
                 (subr (maxeff (read @globals) (read @s) (read @t) spin) (top) bool))
            (val k-names-a-file?
                 (subr (maxeff (read @globals) (read @s) (read @t) spin) (syn) bool))
            (val k-ahead-names-of
                 (subr (maxeff (alloc @t) (read @globals) (read @s) (read @t) spin)
                       (k-tops k-names bool)
                       k-names))
            (val k-given-again
                 (subr (maxeff (alloc @t) (read @globals) (read @t) spin) (k-names k-names k-names)
                       k-names))
            (val k-again-lines (subr (maxeff (alloc @t) (read @globals) spin) (k-names) k-out))
            (val k-ahead-stop (ref int @t))
            (val k-included? (subr (maxeff (read @globals) (read @s) spin) (top) bool))
            (val k-type-top-start (subr (read @globals) (top) int))
            (val k-declared-later?
                 (subr (maxeff (read @globals) (read @s) (read @t) spin) (top) bool))))
