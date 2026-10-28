;; ! `c` has no type `x`
;; A dependent parameter's `select` of a type its module type does not
;; give: refused where the type is read, not at a call, which would put in
;; the argument's own `x` (`TODO.md` §135).
(define-type sig (moduleof (abs t type) (val v t)))
(define f (subr pure ((c : sig) (select c x)) int) (lambda (c y) 0))
0
