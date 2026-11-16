;; ! is a macro's name, which is not bound
(define-syntax let1
  (macro (_ (x @ bvar expr) body @ expr) expr (bind x in body))
  (syntax-rules
    ((_ (x e) body) (let ((x e)) body))))
(let1 (let1 2) 3)
