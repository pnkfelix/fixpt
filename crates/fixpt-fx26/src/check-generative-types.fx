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
