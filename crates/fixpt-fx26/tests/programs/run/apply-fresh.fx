;;; `apply` gives a variadic procedure a fresh list (F11): the procedure's is
;;; typed `acyclic`, and the caller's, at `@heap`, may be written after. Once
;;; it was the caller's own, and `len`, proved to end, ran forever. A list
;;; already at `acyclic` is given as it is: nothing can write it.
(define len (subr pure ((listof int acyclic)) int)
  (lambda (ys)
    (letrec ((go (subr pure ((listof int acyclic) int) int)
               (lambda (ys n) (if (null? ys) n (go (cdr ys) (+ n 1))))))
      (go ys 0))))
(define xs (listof int @heap) (list 1 2))
(define ys (listof int acyclic) (apply list xs))
(set-cdr! (cdr xs) xs)
(define zs (listof int acyclic) (apply list ys))
(+ (* 10 (len ys)) (len zs))
