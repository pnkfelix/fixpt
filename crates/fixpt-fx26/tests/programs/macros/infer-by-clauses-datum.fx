;; => 42
;; A literal of one clause where another has a datum: merged position by
;; position, `(union (literal hi) data)`, not told apart by shape; the
;; clauses' shapes whole, `(union ((literal hi)) (data expr))`, are.
(define-syntax foo (syntax-rules (hi) ((_ hi) "Hello") ((_ 2 expr) (+ 1 expr))))
(if (string=? (foo hi) "Hello") (foo 2 41) 0)
