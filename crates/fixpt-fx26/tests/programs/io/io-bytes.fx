; Accepted: the standard input by bytes (TODO.md §95): a byte or the end;
; as many bytes as have come, into a bytevector's span, which the read
; writes; and whether a read would wait. All under `(io stdin)`.
(define-type byte-result (sumof (byte u8) (eof unit) (failed io-error)))
(define-type count-result (sumof (count int) (eof unit) (failed io-error)))
(define* next (subr (io stdin) () int)
  (lambda () (tagcase (the byte-result (read-byte)) (byte b (u8->int b)) (eof u -1) (failed e -2))))
(define* fill (subr (maxeff (io stdin) (write @b)) ((bytevectorof @b)) int)
  (lambda (bv)
    (tagcase (the count-result (read-bytes bv 0 (bytevector-length bv)))
      (count k k)
      (eof u 0)
      (failed e -1))))
(define* waiting? (subr (io stdin) () bool) (lambda () (not (stdin-ready?))))
