;;; `letfreeze`: a list built, and changed, in a region of its own, which
;;; leaves frozen: at `const`, which nothing may write. Reading it is pure.
(define frozen-list (subr pure (int) (listof int const))
  (lambda (n)
    (letfreeze r
      (let ((xs (the (listof int r) (list 1 2 3))))
        (begin (set-car! xs n) xs)))))
(define* add-up (subr spin ((listof int const) int) int)
  (lambda (xs acc) (if (null? xs) acc (add-up (cdr xs) (+ acc (car xs))))))
(add-up (frozen-list 10) 0)
