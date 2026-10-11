;; ! a f64 is expected here, and this is a int
;; What is written is of the scalar's type.
(define-type pt (bloblet (fields) @b))
(define b pt (make-bloblet 8))
(blobref-set! (the (blobref pt f64) (blobref-at b 0)) 1)
