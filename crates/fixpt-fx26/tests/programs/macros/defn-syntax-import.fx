;; ! a macro's binder, `(macro …)`, says what a use defines, in what its signature makes, `(defn D …)`
;; A macro's binder in an import: no part is in a macro's scope.
(define-syntax m
  (macro/addressed ((bvar (import expr (rho ((path #:a) (macro (_ expr) expr)))))) expr)
  (syntax-rules ((_ x e) e)))
