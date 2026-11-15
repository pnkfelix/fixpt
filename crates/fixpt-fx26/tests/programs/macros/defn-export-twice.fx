;; ! what a use defines is said once, in what it makes, `(defn (ℓ δ) …)`
;; Not by an `export` around the parts too.
(define-syntax define-const
  (macro (export (bvar expr) (rho (A var))) (defn (A var)))
  (syntax-rules
    ((_ n e) (define n e))))
