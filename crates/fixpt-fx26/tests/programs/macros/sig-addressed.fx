;; => 4
;; Herman's form, as it stays writable: each address a path from the root,
;; first step first (`AA`, read right to left, is `(path #:a #:a)`).
(define-syntax let1
  (macro/addressed ((bvar expr) (import expr (rho ((path #:a #:a) var)))) expr)
  (syntax-rules ((_ (x e) body) (let ((x e)) body))))
(let1 (y 3) (+ y 1))
