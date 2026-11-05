; Rejected: a `oneof`'s members must be told apart at run time, or no test
; tells them apart: two procedure types do not.
(define-type v (oneof (subr pure (int) int) (subr pure (bool) int)))
