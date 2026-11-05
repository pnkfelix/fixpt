;; => (5 #t)
;; A call of an `allof` with a union argument: each member of the union
;; fits a member of the `allof`, and the call's type is the union of their
;; results.
(define-type same (allof (subr pure (int) int) (subr pure (bool) bool)))
(define id same (lambda (x) x))
(define* go (subr pure ((oneof int bool)) (oneof int bool)) (lambda (v) (id v)))
(list (go 5) (go #t))
