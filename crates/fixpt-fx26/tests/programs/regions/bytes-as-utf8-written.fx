; Rejected: `bytes-as-utf8` (TODO.md §310) views bytes in place, so only
; bytes frozen into the heap, `bytes`: a buffer still written could make
; the text not UTF-8 after it was validated.
(define* text (poly ((r region)) (subr (alloc r) () (sumof (text utf8) (bad int))))
  (lambda () (bytes-as-utf8 (the (bytevectorof r) (make-bytevector 2 (int->u8 65))))))
