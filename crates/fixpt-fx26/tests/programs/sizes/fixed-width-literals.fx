;;; An `i32` or a `u32` is an `int` (the fixnum it stands for), so it goes
;;; where an `int` is wanted; and a literal in its range is one, where an
;;; `i32` or a `u32` is wanted.
(define x u32 7)
(define y i32 -5)
(define bump (subr pure (u32) u32) (lambda (a) (u32+ a 1)))
(if (< y 0) (+ (bump 4294967295) (+ x 1)) 0)
