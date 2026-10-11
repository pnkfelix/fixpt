;;; A literal past a `u64`'s range, past a fixnum too, is not one: refused.
(define z u64 18446744073709551616)
z
