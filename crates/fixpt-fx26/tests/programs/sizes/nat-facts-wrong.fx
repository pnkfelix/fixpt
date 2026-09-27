; Rejected: where `(< i n)`, `i - n` is below 0, no natural.
(define gap (subr pure (nat nat) nat) (lambda (i n) (if (< i n) (- i n) 0)))
