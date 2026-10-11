;; ! a (bloblet (fields int) @b) is expected here, and this is a (bloblet (fields int a) @b)
;; Refused: a forgotten field of a type variable, which could be a
;; procedure.
(define-type one (bloblet (fields int) @b))
(define widen (poly ((a type)) (subr pure ((bloblet (fields int a) @b)) one))
  (plambda ((a type)) (lambda (b) b)))
