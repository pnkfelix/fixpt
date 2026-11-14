;;; A family's conversions named: polymorphic in its parameters, as derived
;;; ones are.
(define-generative (box (t type +)) (productof (v t)) #:seal box-of #:unseal box-contents)
(define a (box int) (box-of (product (v 7))))
(extract (box-contents a) v)
