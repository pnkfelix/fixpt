;; ! the module gives no type `x`
;; `(type x)` keeps a type, and `x` is a value.
(define-type r (restrict (moduleof (desc t int) (val x int)) (type x)))
0
