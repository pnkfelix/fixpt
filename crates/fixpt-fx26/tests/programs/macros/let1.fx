;; => 7
(define-syntax let1
  ;; As named: ((x bvar) (e expr)) (body (in expr x))
  (macro (_ (x @ bvar expr) body @ expr) expr (bind x in body))
  (syntax-rules
    ((_ (x e) body) (let ((x e)) body))))
(let1 (y 3) (+ y 4))
