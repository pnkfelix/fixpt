;; => 2
;; A type form's name: where the top level binds no function `listof`, the
;; type form, whatever binds `listof` where it is written.
(define g (poly ((listof (=> (type) type))) (subr pure () int))
  (plambda ((listof (=> (type) type)))
    (lambda () (length (the (#%toplevel:listof int) (list 1 2))))))
((proj g (dlambda ((a type)) a)))
