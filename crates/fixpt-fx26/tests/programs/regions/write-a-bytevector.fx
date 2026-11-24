; Rejected: a `bytevector` is `(bytevectorof const)` (TODO.md §310),
; frozen, and nothing may write it.
(define made (letfreeze r (the (bytevectorof r) (make-bytevector 4 (int->u8 7)))))
(bytevector-u8-set! made 0 (int->u8 1))
