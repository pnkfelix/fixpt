;;; Refused today: a `define-datatype` constructor returns the whole
;;; datatype, so its result cannot be used at a refinement, though the
;;; `one` form it expands to gives the one-tag type `(oneof (circle int))`.
(define-datatype shape (circle int) (rect int int))
(define-type just-circle (oneof (circle int)))
(define ok just-circle (one circle 3))
(define c1 just-circle (circle 3))
