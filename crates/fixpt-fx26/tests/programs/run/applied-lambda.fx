;;; A lambda applied at once is a `let`: no closure made, no call. Its
;;; arguments are made in order, before the body (the log's digits say
;;; so), and a lambda inside it still captures what it binds.
(define log (ref int @r) (new 0))
(define* note (subr (maxeff (read @r) (write @r)) (int) int)
  (lambda (k) (begin (set log (+ (* 10 (get log)) k)) k)))
(define* f (subr (maxeff (read @r) (write @r)) (int) int)
  (lambda (n)
    ((lambda ((a int) (b int)) (+ (* 100 ((lambda ((x int)) (+ a x)) b)) (note 3)))
     (note 1) (note (+ n 1)))))
(+ (* 1000 (f 1)) (get log))
