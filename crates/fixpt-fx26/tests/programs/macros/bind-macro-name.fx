;; ! is a macro's name, which is not bound
(define-syntax let1
  ((bvar expr) (import expr (rho (AA var))))
  (syntax-rules ()
    ((_ (x e) body) (let ((x e)) body))))
(let1 (let1 2) 3)
