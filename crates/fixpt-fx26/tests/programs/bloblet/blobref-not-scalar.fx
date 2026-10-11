;; ! only a scalar's bytes are read or written, and this points to a f
;; Only a scalar's bytes come out as a value: a blobref to a flat variable
;; is not read.
(define-type pt (bloblet (fields) @b))
(define get (poly ((f flat)) (subr (read @b) ((blobref pt f)) int))
  (plambda ((f flat)) (lambda (r) (blobref-get r) 0)))
