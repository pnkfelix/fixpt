;; => 42
;; A signature inferred of clauses of different shapes: merged position by
;; position, `((union (literal hi) (literal ho)) . (union () (expr)))`, the
;; clause each part goes with is lost and `hi`'s clause does not fit it;
;; the union of the clauses' shapes whole, `(union ((literal hi)) ((literal
;; ho) expr))`, inferred instead, fits them.
(define-syntax foo (syntax-rules (hi ho) ((_ hi) "Hello") ((_ ho expr) (+ 1 expr))))
(if (string=? (foo hi) "Hello") (foo ho 41) 0)
