;;; A point as a bloblet in a region of its own, moved in place: a write
;;; the type records, and a read of the result.
(define p (bloblet (fields int int) @pts) (make-bloblet 0 3 4))
(define move (subr (maxeff (read @pts) (write @pts)) ((bloblet (fields int int) @pts) int) unit)
  (lambda (q dx) (bloblet-set! q 0 (+ (bloblet-ref q 0) dx))))
(move p 10)
(+ (bloblet-ref p 0) (bloblet-ref p 1))
