; A program's own definition of a standard type's name is the program's
; (TODO.md §88): `bytevector` here is a bloblet of bytes, as
; scheme-bench/bv2string.fx defines it, not the standard `bytevector`.
(define-type bytevector (bloblet (fields) @heap))
(define first-byte (subr (read @heap) (bytevector) int) (lambda (bv) (bloblet-byte bv 0)))
(define made (subr (maxeff (alloc @heap) (read @heap) (read (globals first-byte))) () int)
  (lambda () (first-byte (the bytevector (make-bloblet 1)))))
(made)
