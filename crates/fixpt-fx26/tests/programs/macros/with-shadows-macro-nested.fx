;; ! `clamp` is a macro here, and `m` gives a value of that name
;; In a use's operand, in a `with` inside another, all the same.
(define m (module (define clamp (lambda ((x int)) (* x 2)))))
(define n (module (define other 1)))
(define-syntax clamp (expr) (syntax-rules () ((_ e) (let ((v e)) (if (> v 10) 10 v)))))
(define-syntax twice (expr) (syntax-rules () ((_ e) (let ((w e)) (+ w w)))))
(with m (with n (twice (clamp 100))))
