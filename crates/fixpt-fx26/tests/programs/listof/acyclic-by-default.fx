;; => (3 3)
;; `(listof T)` is `(listof T acyclic)`, so a list of either kind passes
;; where the other is asked for.
(define-type ints (listof int))
(define sum-of (subr pure ((listof int acyclic)) int)
  (lambda (l) (if (null? l) 0 (+ (car l) (if (null? (cdr l)) 0 (car (cdr l)))))))
(define xs ints (list 1 2))
(define ys (listof int acyclic) xs)
(list (sum-of xs) (sum-of ys))
