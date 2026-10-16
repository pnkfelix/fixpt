;;; `remainder` in line (`TODO.md` §103): of two values, by a constant,
;;; and of a bignum, the primitive's (`direct.rs`,
;;; `remainder_in_line_as_the_rust_machine_gives_it`).
(define* r (subr pure (int int) int) (lambda (a b) (remainder a b)))
(define* r7 (subr pure (int) int) (lambda (a) (remainder a -7)))
(define* big (subr pure (int int) int) (lambda (a b) (remainder (* a 1000000000000000) b)))
(r 17 5)
