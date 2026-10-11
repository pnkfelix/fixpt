;; ! `f` is a flat, not a type
;; A flat is no type: a flat thing is no value, and is reached through a
;; `blobref`.
(define bad (poly ((f flat)) (subr pure (f) f)) (plambda ((f flat)) (lambda (x) x)))
