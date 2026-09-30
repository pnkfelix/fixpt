; Rejected: types declared ahead may name each other, but a cycle must
; pass through a constructor, not only through names.
(define-type a b)
(define-type b a)
1
