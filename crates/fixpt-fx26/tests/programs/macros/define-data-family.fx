;; => 4
;; `define-data` of a family (`docs/research/datatype-macro.md`, §7's
;; stretch): its parameters, which the use names, in scope in its
;; variants' types; a recursive one, a list.
(define-syntax payload
  (-> (type ...) type)
  (syntax-rules ()
    ((_) unit)
    ((_ f) f)
    ((_ f g ...) (tupleof f g ...))))
(define-syntax define-data
  (-> ((union dvar (dvar (dvar kind) ...)) (label type ...) ...) defn)
  (syntax-rules ()
    ((_ (name (p k) ...) (t field ...) ...)
     (define-type (name (p k) ...) (sumof (t (payload field ...)) ...)))
    ((_ name (t field ...) ...) (define-type name (sumof (t (payload field ...)) ...)))))
(define-data (box (a type)) (#:full a) (#:empty))
(define-data (chain (a type)) (#:end) (#:link a (chain a)))
(define b (box int) (#:full 3))
(define c (chain bool) (#:link #t (#:link #f (#:end))))
(+ (tagcase b (#:full n n) (#:empty u 0))
   (tagcase c (#:link (x rest) (tagcase rest (#:link (y r) 1) (#:end u 0))) (#:end u 0)))
