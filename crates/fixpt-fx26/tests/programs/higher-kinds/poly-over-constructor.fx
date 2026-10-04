;; => (1 2)
;; A procedure polymorphic in a type constructor `f`, of kind
;; `(=> (type) type)`, given a type family, a `dlambda`, and a type form's
;; name (`listof`, of kind `(=> (type region) type)`).
(define-type (box (t type)) (productof (v t)))
(define id (poly ((f (=> (type) type)) (a type)) (subr pure ((f a)) (f a)))
  (plambda ((f (=> (type) type)) (a type)) (lambda (x) x)))
(define id2 (poly ((f (=> (type region) type)) (a type) (r region)) (subr pure ((f a r)) (f a r)))
  (plambda ((f (=> (type region) type)) (a type) (r region)) (lambda (x) x)))
(define b ((proj id box int) (product (v 3))))
(define l ((proj id (dlambda ((t type)) (listof t @heap)) int) (list 1 2)))
((proj id2 listof int @heap) l)
