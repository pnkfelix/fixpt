; Rejected: a union's members must differ in shape at run time, or no test
; tells them apart: two procedure types do not.
(define-type v (union (subr pure (int) int) (subr pure (bool) int)))
