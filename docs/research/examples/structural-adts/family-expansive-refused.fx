;;; Refused today: a family whose argument grows as it recurses (a nested
;;; type) has infinitely many instances, and is not a regular type.
(define-type (grow (a type))
  (sumof (stop a) (more (grow (productof (l a) (r a))))))
(define g (grow int) (sum stop 1))
