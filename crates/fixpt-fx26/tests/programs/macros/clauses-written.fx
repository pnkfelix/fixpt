;; => 42
;; A signature of a member per clause, written, `(clauses σ₁ σ₂ …)`
;; (`typed-macros.md`, "Decided: a signature per clause, chosen as the
;; clauses are"): each clause checked against its own, a use by its
;; clause's, the first whose pattern it matches.
(define-syntax foo (clauses ((literal hi)) ((literal ho) expr))
  (syntax-rules (hi ho) ((_ hi) "Hello") ((_ ho expr) (+ 1 expr))))
(if (string=? (foo hi) "Hello") (foo ho 41) 0)
