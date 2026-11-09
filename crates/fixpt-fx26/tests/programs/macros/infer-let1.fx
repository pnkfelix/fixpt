;; => 7
;; A signature inferred (`syntax-rules`, none written): `x` a binder, as
;; `let` places it; `body` in its scope, `(import expr (rho (AA var)))`.
(define-syntax let1
  (syntax-rules ()
    ((_ (x e) body) (let ((x e)) body))))
(let1 (y 3) (+ y 4))
