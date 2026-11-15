;; ! `(syntax σ)` says what a use defines, in what its signature makes, `(defn (ℓ (syntax σ)))`
;; A macro's binder in an import: no part is in a macro's scope.
(define-syntax m
  ((bvar (import expr (rho (A (syntax (expr)))))))
  (syntax-rules ((_ x e) e)))
