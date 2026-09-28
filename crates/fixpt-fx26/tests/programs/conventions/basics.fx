;;; Conventions (`docs/research/native-conventions.md`): the program's is
;;; `cellular`, written or left out; any of FX-26's own may be seen as `fx`,
;;; and a call through `fx` needs nothing more.
(define inc (subr pure (int) int) (lambda (x) (+ x 1)))
(define inc-c (subr (conv cellular) pure (int) int) inc)
(define inc-fx (subr (conv fx) pure (int) int) inc)
(define twice (subr pure ((subr (conv fx) pure (int) int) int) int) (lambda (f x) (f (f x))))
(twice inc 3)
(twice inc-fx 3)
(inc-fx 4)
(convention fx inc)
(twice (convention fx inc) 5)
