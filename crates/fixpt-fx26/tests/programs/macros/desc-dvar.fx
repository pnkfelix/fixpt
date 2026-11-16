;; => 4
;; A description binder the use gives (`dvar`), in scope in a part.
;; As named: ((t dvar) (e (in expr t)))
(define-syntax pfun
  (macro (_ t @ dvar e @ expr) expr (bind t in e))
  (syntax-rules
    ((_ t e) (plambda ((t type)) e))))
((proj (pfun u (lambda ((x u)) x)) int) 4)
