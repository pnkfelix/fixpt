; Rejected: `certify-nat` only where `nat?` has just said so.
(define bad (subr pure (int) nat) (lambda (i) (certify-nat i)))
