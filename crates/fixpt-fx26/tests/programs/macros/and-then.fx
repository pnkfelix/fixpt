;; => (5 #f)
;; A truthy `and` (TODO.md §197): `#f` if an operand is, else the last's
;; value, so results of `(oneof false T)` chain.
(define-type maybe-int (oneof false int))
(define-syntax and-then
  ;; As named: ((e expr) (es (listof expr)))
  (expr . (mu es (union () (expr . es))))
  (syntax-rules ()
    ((_ e) e)
    ((_ e1 e2 . rest) (let ((t e1)) (if (eq? t #f) #f (and-then e2 . rest))))))
(define* half (subr pure (int) maybe-int) (lambda (n) (if (= (remainder n 2) 0) (quotient n 2) #f)))
(define* halves (subr pure (int) maybe-int)
  (lambda (n) (and-then (half n) (half n) (half (* n 5)))))
(list (halves 2) (halves 3))
