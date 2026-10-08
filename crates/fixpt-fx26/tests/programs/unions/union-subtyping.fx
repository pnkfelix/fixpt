; Accepted: a member is below its union, and a union below a wider one; a
; `cons` where a union with a list is wanted is solved as that list's pair.
(define-type small (union int string))
(define-type wide (union int string symbol (listof int @r)))
(define* widen (subr pure (small) wide) (lambda (x) x))
(define* one (subr (alloc @r) () wide) (lambda () (cons 1 nil)))
(widen (the small 3))
