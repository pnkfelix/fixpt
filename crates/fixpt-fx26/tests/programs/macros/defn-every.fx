;; => 7
;; What a use defines, every repetition's binder, `(defn name (c ...))`: a template that uses
;; `define-data` sees each constructor it defines, `k`, and calls it.
(define-syntax payload
  (macro (_ desc ...) desc)
  (syntax-rules
    ((_) unit)
    ((_ f) f)
    ((_ f g ...) (tupleof f g ...))))
(define-syntax define-data
  (macro (_ name @ dvar (c @ bvar label desc ...) ...) (defn name (c ...)))
  (syntax-rules
    ((_ name (c t field ...) ...)
     (begin
       (define-type name (sumof (t (payload field ...)) ...))
       (define c (subr pure (field ...) name) (lambda ((x field) ...) (t x ...)))
       ...))))
(define-syntax define-one
  (macro (_ t @ dvar k @ bvar v @ bvar) (defn t k v))
  (syntax-rules ((_ t k v) (begin (define-data t (k #:k int)) (define v (k 7))))))
(define-one thing make-thing it)
(tagcase it (#:k n n))
