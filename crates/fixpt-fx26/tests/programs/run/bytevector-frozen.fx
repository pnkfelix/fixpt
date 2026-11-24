; `bytevector` is `(bytevectorof const)` (TODO.md §310), as `string` is
; `(stringof const)`: a bytevector built at a region and frozen by
; `letfreeze` is one, nothing copied, read purely by any reading
; operation, and a `(bytevectorof const)` is written so.
(define* n (subr pure (bytevector) nat) (lambda (b) (bytevector-length b)))
(define* first (subr pure (bytevector) u8) (lambda (b) (bytevector-u8-ref b 0)))
(define made (letfreeze r (the (bytevectorof r) (make-bytevector 4 (int->u8 7)))))
made
(n made)
(first made)
(the (bytevectorof const) made)
(bytevector=? made (bytevector-copy made 0 4))
