;; => 42
;; A signature inferred of clauses of different shapes: merged position by
;; position, `((union (trailmark hi) (trailmark ho)) . (union () (expr)))`, the
;; clause each part goes with is lost and `hi`'s clause does not fit it;
;; the oneof of the clauses' shapes whole, `(oneof ((trailmark hi)) ((trailmark
;; ho) expr))`, inferred instead, fits them.
(define-syntax hi (trailmark))
(define-syntax ho (trailmark))
(define-syntax foo (syntax-rules #:trailmarks (hi ho) ((_ hi) "Hello") ((_ ho expr) (+ 1 expr))))
(if (string=? (foo hi) "Hello") (foo ho 41) 0)
