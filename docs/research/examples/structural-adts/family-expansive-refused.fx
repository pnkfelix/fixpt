;;; Refused today: a family whose argument grows as it recurses (a nested
;;; type) has infinitely many instances, and is not a regular type.
(define-type (grow (a type))
  (oneof (stop a) (more (grow (tupof (l a) (r a))))))
(define g (grow int) (one stop 1))
