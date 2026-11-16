;; ! a use of `let1`
;; A binder where the signature wants one, given an expression.
(define-syntax let1
  (macro (_ (x @ bvar expr) body @ expr) expr (bind x in body))
  (syntax-rules
    ((_ (x e) body) (let ((x e)) body))))
(let1 ((f 1) 2) 3)
