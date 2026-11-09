;; => 6
;; A datatype whose variants name it, by `define-data`: a type's name is in
;; scope in itself.
(define-syntax payload
  (-> (type ...) type)
  (syntax-rules ()
    ((_) unit)
    ((_ f) f)
    ((_ f g ...) (tupleof f g ...))))
(define-syntax define-data
  (-> (dvar (label type ...) ...) defn)
  (syntax-rules ()
    ((_ name (t field ...) ...) (define-type name (sumof (t (payload field ...)) ...)))))
(define-data tree (#:leaf int) (#:node tree tree))
(define-rec (total (->* (tree) int)
  (lambda (t) (tagcase t (#:leaf n n) (#:node (l r) (+ (total l) (total r)))))))
(total (#:node (#:leaf 1) (#:node (#:leaf 2) (#:leaf 3))))
