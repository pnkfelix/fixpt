;; => 7
(define-syntax let1
  ;; As named: ((x bvar) (e expr)) (body (in expr x))
  (macro ((bvar expr) (import expr (rho (AA var)))) expr)
  (syntax-rules
    ((_ (x e) body) (let ((x e)) body))))
(let1 (y 3) (+ y 4))
