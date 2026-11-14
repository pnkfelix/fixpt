;; => 42
;; A literal of one clause where another has a datum: merged position by
;; position, `(oneof (trailmark hi) data)`, not told apart by shape; the
;; clauses' shapes whole, `(oneof ((trailmark hi)) (data expr))`, are.
(define-syntax hi (trailmark))
(define-syntax foo (syntax-rules #:trailmarks (hi) ((_ hi) "Hello") ((_ 2 expr) (+ 1 expr))))
(if (string=? (foo hi) "Hello") (foo 2 41) 0)
