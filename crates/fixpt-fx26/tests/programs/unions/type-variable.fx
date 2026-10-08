; Rejected: a type variable may stand for any type, of any shape, so none is a
; union's member (yet).
(define* f (poly ((t type)) (subr pure ((union int t)) int)) (lambda (x) 0))
