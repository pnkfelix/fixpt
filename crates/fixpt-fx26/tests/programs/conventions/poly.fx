;;; Code polymorphic in a convention; the binder is solved by what it is
;;; given, and defaults to the program's.
(define app (poly ((c conv) (e effect)) (subr e ((subr (conv c) e (int) int) int) int))
  (plambda ((c conv) (e effect)) (lambda (f x) (f x))))
(define inc (subr pure (int) int) (lambda (x) (+ x 1)))
(define inc-fx (subr (conv fx) pure (int) int) inc)
(app inc 1)
(app inc-fx 1)
((proj app fx pure) inc 2)
(proj app cellular pure)
(proj app fx pure)
