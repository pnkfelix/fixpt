;; => (1)
;; A generative type with a type constructor among its parameters: its
;; conversions are polymorphic in it.
(define-generative (wrapped (f (=> (type) type)) (a type)) (f a)
  #:seal up-wrapped #:unseal down-wrapped)
(define-type (lst (t type)) (listof t @heap))
(define w ((proj up-wrapped lst int) (list 1)))
((proj down-wrapped lst int) w)
