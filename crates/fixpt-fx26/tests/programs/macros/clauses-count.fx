;; ! a signature of `clauses` has a member for each clause: here 1 for 2
(define-syntax foo (clauses ((literal hi)))
  (syntax-rules (hi ho) ((_ hi) "Hello") ((_ ho expr) (+ 1 expr))))
1
