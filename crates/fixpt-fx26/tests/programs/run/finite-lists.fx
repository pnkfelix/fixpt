;;; Finite lists: a `letfreeze` whose body only builds its region's data,
;;; never writing it, gives `finite` data, which no cycle runs through; one
;;; that writes it gives `const`, which may be cyclic. Finite data is also
;;; `const` data, so a procedure over `(listof int const)` takes both.
(define len (subr spin ((listof int finite) int) int)
  (lambda (xs n) (if (null? xs) n (len (cdr xs) (+ n 1)))))
(define first (subr pure ((listof int const)) int) (lambda (xs) (car xs)))
(define built (subr pure (int) (listof int finite))
  (lambda (n) (letfreeze r (the (listof int r) (cons n (cons (+ n 1) nil))))))
(define changed (subr pure (int) (listof int const))
  (lambda (n) (letfreeze r (let ((ys (the (listof int r) (cons 1 nil)))) (begin (set-car! ys n) ys)))))
(+ (len (built 5) 0) (+ (first (built 7)) (first (changed 9))))
