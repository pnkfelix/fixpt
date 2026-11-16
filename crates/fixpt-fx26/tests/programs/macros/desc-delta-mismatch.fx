;; ! the signature says a value's binder is here
;; A signature that says a value's binder where a description's is.
(define-syntax bad
  (macro/addressed (dvar (import expr (rho ((path #:a) var)))) expr)
  (syntax-rules
    ((_ t e) (plambda ((t type)) e))))
1
