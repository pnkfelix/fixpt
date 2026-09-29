;;; `confirm-length`: a frozen list found to have three elements is a
;;; `(nlist int 3)`; one of three is not a list of two.
(define line (subr pure (int) (listof int const))
  (lambda (n)
    (letfreeze r
      ;; cons-chain: built in r, then frozen
      (let ((ys (the (listof int r) (cons 1 (cons 2 (cons 3 nil))))))
        (begin (set-car! ys n) ys)))))
(define second (subr pure ((nlist int 3)) int) (lambda (v) (car (cdr v))))
(define* f (subr pure ((listof int const)) int)
  (lambda (xs) (confirm-length xs 3 (v (second v)) -1)))
(define g (subr pure ((listof int const)) int) (lambda (xs) (confirm-length xs 2 (v 1) -1)))
(+ (* 10 (f (line 5))) (g (line 5)))
