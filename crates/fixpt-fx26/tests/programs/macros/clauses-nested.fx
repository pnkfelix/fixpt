;; ! `(clauses σ …)` is a signature's whole, one member for each clause, not a part of one
(define-syntax foo (expr (clauses (expr) (data)))
  (syntax-rules () ((_ a b) a)))
1
