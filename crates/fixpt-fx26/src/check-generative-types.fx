;;; The types of `check-generative.fx`, its `check-generative-module`: a module file of no
;;; state, which it loads, and so may its clients (`TODO.md` §68); its
;;; items in the order they were there.

;; The types these use, from the files that define them.
(define check-types-types (load-module "fx26:check-types-types.fx"))
(define-type k-ids (select check-types-types k-ids))
(define check-subst-types (load-module "fx26:check-subst-types.fx"))
(define-type k-pairs (select check-subst-types k-pairs))
(define-type k-seen-pol (ref k-pairs @t))
;; Where a walk for polarities puts each it finds.
(define-type k-pols-found (ref k-ids @t))

;;; ------------------------------------------------------------ signatures

;; What its clients use of it (`check-program.fx`).
;; The types it names, from the files that define them.
(define parser-types ((proj (load-module "fx26:parser-types.fx") @s @e @m @c @p)))
(define-type syn (select parser-types syn))
(define-type check-generative-sig
  (moduleof (val k-define-generative
                 (subr (maxeff (alloc @t)
                               (goto @z)
                               (read @globals)
                               (read @s)
                               (read @t)
                               (write @t)
                               spin)
                       (syn syn)
                       symbol))))
