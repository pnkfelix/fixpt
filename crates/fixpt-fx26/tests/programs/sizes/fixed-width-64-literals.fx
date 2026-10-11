;;; A literal in an `i64`'s or a `u64`'s range is one where one is wanted,
;;; past a fixnum too: the parsers write such a literal as arithmetic on
;;; fixnums, which the checkers read back as the literal it is.
(define x i64 5)
(define big u64 18446744073709551615)
(define neg i64 -9223372036854775808)
(define add (subr pure (i64 i64) i64) (lambda (a b) (i64+ a b)))
(list (i64->int (i64+ 1 2)) (i64->int (add x 9223372036854775800)) (u64->int big) (i64->int neg))
