;;; `length` of a `(nlist t n)` is a `(nat n)`; a length computed at run
;;; time can confirm a list's: here, that a frozen list is as long as `xs`.
(define three (nlist int 3) (cons 1 (cons 2 (cons 3 nil))))
(define n (nat 3) (length three))
(define as-long (poly ((n size)) (subr pure ((nlist int n) (listof int const) (nlist int n)) (nlist int n)))
  (lambda (xs ys otherwise)
    (let ((k (length xs)))
      (confirm-length ys k (zs zs) otherwise))))
(define line (subr pure (int) (listof int const))
  (lambda (n) (letfreeze r (let ((ys (the (listof int r) (cons 1 (cons 2 (cons 3 nil)))))) (begin (set-car! ys n) ys)))))
(define* total (poly ((n size)) (subr pure ((nlist int n)) int))
  (lambda (xs) (if (null? xs) 0 (+ (car xs) (total (cdr xs))))))
(+ (* 100 (total (as-long three (line 5) three))) (length (as-long (cdr three) (line 5) (cdr three))))
