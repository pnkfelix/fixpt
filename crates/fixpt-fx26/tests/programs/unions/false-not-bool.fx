; Rejected: `false` and `bool` share a shape, so no test tells them apart
; in a union.
(define-type v (union false bool))
