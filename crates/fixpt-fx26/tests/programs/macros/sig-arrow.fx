;; ! a macro's signature is `(macro σ made)`: `->` is a procedure's type
;; A macro's signature written as a procedure's type.
(define-syntax twice
  (-> (expr) expr)
  (syntax-rules ((_ e) (+ e e))))
