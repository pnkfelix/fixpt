;; ! a macro's binder, `(macro σ made)`, says what a use defines, in what its signature makes, `(defn (ℓ (macro σ made)))`
;; A macro's binder in an import: no part is in a macro's scope.
(define-syntax m
  (macro ((bvar (import expr (rho (A (macro (expr) expr)))))) expr)
  (syntax-rules ((_ x e) e)))
