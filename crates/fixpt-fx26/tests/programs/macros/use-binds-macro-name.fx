;; => 3
;; A use's binder may be a macro's name, which it shadows where it binds
;; (TODO.md §295): the body's `let1` is the bound 2, not the macro.
(define-syntax let1
  (macro (_ (x @ bvar expr) body @ expr) expr (bind x in body))
  (syntax-rules
    ((_ (x e) body) (let ((x e)) body))))
(let1 (let1 2) (+ let1 1))
