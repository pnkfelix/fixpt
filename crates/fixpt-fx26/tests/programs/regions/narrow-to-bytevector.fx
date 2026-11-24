; Rejected: `bytevector?` narrows to the frozen `bytevector`, `(bytevectorof
; const)` (TODO.md §310), so a buffer still written at its region is never
; taken for one: its shape is not known, as a generative type's is not.
(define* leak (poly ((r region)) (subr (alloc r) ((bytevectorof r)) bytevector))
  (lambda (b) (typecase b (bytevector c c) (else d (make-bytevector 0 (int->u8 0))))))
