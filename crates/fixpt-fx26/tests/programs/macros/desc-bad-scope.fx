;; ! `t` is referred to where the template does not bind it
;; A use's description binder referred to outside the scope it binds.
(define-syntax bad
  (macro (_ t @ dvar e @ expr) expr (bind t in e))
  (syntax-rules
    ((_ t e) (begin (plambda ((t type)) e) (the t 1)))))
1
