; Rejected: `certify-nat` named only to call it (F16): bound to another
; name, its call escaped the rule, and `(cn -3)` was a `nat`.
(define bad (subr pure () nat) (lambda () (let ((cn certify-nat)) (cn -3))))
