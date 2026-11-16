;; ! what a use defines is said once, in what it makes, `(defn (ℓ δ) …)`
;; Not by an `export` around the parts too.
(define-syntax define-const
  (macro/addressed (export (bvar expr) (rho ((path #:a) var))) (defn ((path #:a) var)))
  (syntax-rules
    ((_ n e) (define n e))))
