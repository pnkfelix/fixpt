;;; The signature of `check-read-made.fx`, as its clients use it (`TODO.md`
;;; §68): a module file of no state.

;;; ------------------------------------------------------------ signatures

;; What its clients use of it (`check-read-descs.fx`).
;; The types it names, from the files that define them.
(hide (define check-types-types (load-module "fx26:check-types-types.fx")))
(import check-types-types (type k-desc))
(hide (define check-read-types (load-module "fx26:check-read-types.fx")))
(define-type k-syns (select check-read-types k-syns))
(hide (define parser-types ((proj (load-module "fx26:parser-types.fx") @s @e @m @c @p))))
(define-type syn (select parser-types syn))
;; How a description is read: `check-read-descs.fx`'s `k-parse-d`, given.
(define-type k-desc-reader
  (subr (maxeff (alloc @t) (goto @z) (read @globals) (read @s) (read @t) (write @t) spin)
        (syn)
        k-desc))
(define-type check-read-made-sig
  (moduleof (val k-type-made-by
                 (subr (maxeff (alloc @t) (goto @z) (read @globals) (read @s) (read @t) (write @t)
                               spin)
                       (syn k-syns bool k-desc-reader)
                       int))))
