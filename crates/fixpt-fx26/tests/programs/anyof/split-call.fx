;; => ("one" "2")
;; Rule 5 at an argument that is no variable (U3): `(pick b)`, of a union,
;; taken as each member in turn, the call checking with each; its value is
;; made once. As a `(car xs)` is.
(define pick (subr pure (bool) (oneof int string)) (lambda (b) (if b 1 "one")))
(define show (allof (subr pure (int) string) (subr pure (string) string))
  (lambda (x) (if (int? x) (int->string (+ x 1)) x)))
(define xs (listof (oneof int string)) (list 1 "b"))
(list (show (pick #f)) (show (car xs)))
