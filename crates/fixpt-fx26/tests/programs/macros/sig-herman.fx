;; ! a signature in shapes and facts is `(macro (_ part …) made fact …)`; Herman's, `(macro/addressed σ made)`
;; Herman's form under `macro`, as signatures were written before the
;; shapes and facts (`typed-macros.md`).
(define-syntax let1
  (macro ((bvar expr) (import expr (rho (AA var)))) expr)
  (syntax-rules ((_ (x e) body) (let ((x e)) body))))
