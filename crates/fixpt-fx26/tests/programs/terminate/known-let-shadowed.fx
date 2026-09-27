; Rejected: the same, the known `w` a `let`'s, and gone by the time the
; parameter `w` is bound.
(define-type T (subr pure (T) int))
(define zero int (let ((w (the T (lambda (x) 0)))) 0))
(define omega T (lambda ((w T)) (w w)))
