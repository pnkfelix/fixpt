;; => ((1))
;; A description function that gives a description function.
(define-type twice-of (dlambda ((f (=> (type) type))) (dlambda ((a type)) (f (f a)))))
(define-type (lst (t type)) (listof t @heap))
(the ((twice-of lst) int) (list (list 1)))
