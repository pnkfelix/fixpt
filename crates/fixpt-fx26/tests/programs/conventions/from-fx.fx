;;; A procedure seen as `fx` is converted back where the program's is
;;; expected: the checker inserts the conversion.
(define inc-fx (subr (conv fx) pure (int) int) (lambda (x) (+ x 1)))
(define inc (subr pure (int) int) inc-fx)
(define apply1 (subr pure ((subr pure (int) int) int) int) (lambda (f x) (f x)))
(apply1 inc-fx 2)
(convention cellular inc-fx)
