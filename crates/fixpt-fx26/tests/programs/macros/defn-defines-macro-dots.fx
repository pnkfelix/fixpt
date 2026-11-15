;; ! `...` in a macro a template defines is the template's (R7RS), and repeats nothing here: the defined macro's is written `(... ...)`
;; A bare ellipsis in the defined macro's template.
(define-syntax def-lister
  (macro (bvar) defn)
  (syntax-rules
    ((_ name) (define-syntax name (syntax-rules ((_ e ...) (list e ...)))))))
