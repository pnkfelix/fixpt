;; => 12
;; `x`, bound after the body is written, in scope in it: the body's import
;; addresses its sibling (car of car of cdr, `AAD`).
(define-syntax where
  ;; As named: ((body (in expr x)) ((x bvar) (e expr)))
  ((import expr (rho (AAD var))) (bvar expr))
  ((_ body (x e)) (let ((x e)) body)))
(where (* x 4) (x 3))
