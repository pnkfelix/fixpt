;;; Operands run in the order written, even where an operation takes them
;;; the other way round: `>` and `<=` are `<` with the operands traded, and
;;; here the first operand's write must come before the second's read (the
;;; register code once ran the second first, and gave #t).
(define r (ref int @r) (new 0))
(define* f (subr (maxeff (read @r) (write @r)) () bool)
  (lambda () (> (begin (set r 10) 5) (get r))))
(define* g (subr (maxeff (read @r) (write @r)) () bool)
  (lambda () (<= (begin (set r 1) 5) (get r))))
(if (f) 1 (if (g) 2 3))
