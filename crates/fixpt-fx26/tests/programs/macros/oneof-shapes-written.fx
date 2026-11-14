;; => 42
;; A signature of one choice among the clauses' whole shapes, written: each
;; use's member told by its shape, whichever clause expands it.
(define-syntax hi (trailmark))
(define-syntax ho (trailmark))
(define-syntax foo (oneof ((trailmark hi)) ((trailmark ho) expr))
  (syntax-rules #:trailmarks (hi ho) ((_ hi) "Hello") ((_ ho expr) (+ 1 expr))))
(if (string=? (foo hi) "Hello") (foo ho 41) 0)
