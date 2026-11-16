;; ! `name` is not repeated: named alone, not `(name ...)`
;; What a use defines, `(label ...)`, of a label that is not repeated.
(define-syntax define-one
  (macro (_ name @ bvar e @ expr) (defn (name ...)))
  (syntax-rules ((_ name e) (define name e))))
(define-one x 1)
