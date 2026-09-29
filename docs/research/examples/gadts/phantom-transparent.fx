;;; FX-26 today: a phantom index under a transparent abbreviation means
;;; nothing. `(counted z)` and `(counted o)` are both just a list, so a list
;;; "counted from zero" passes for one "counted from one", as the
;;; prototype found structurally. Compare `phantom-generative-refused.fx`.
(define-type zero (sumof (zero unit)))
(define-type one (sumof (one unit)))
(define-type (counted (i type)) (listof int acyclic))
(define from-zero (counted zero) (cons 0 (cons 1 nil)))
(define from-one (counted one) from-zero)
(car from-one)
