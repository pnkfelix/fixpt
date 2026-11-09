;; ! `define-const` makes definitions, which are made at the top level, not where an expression is
(define-syntax define-const
  (-> (bvar expr) defn)
  (syntax-rules ()
    ((_ n e) (define n e))))
(+ 1 (define-const y 2))
