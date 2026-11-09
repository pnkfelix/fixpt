;; => 7
;; A macro that makes a description, used where a type is: a payload's
;; type by how many parts it has.
(define-syntax payload
  (-> (type ...) type)
  (syntax-rules ()
    ((_) unit)
    ((_ f) f)
    ((_ f g ...) (tupleof f g ...))))
(define x (payload int bool) (tuple 7 #t))
(extract x 1)
