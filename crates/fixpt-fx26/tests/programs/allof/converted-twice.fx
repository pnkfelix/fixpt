;; ! one value cannot be both
;; Converted for one member and not for the other: it would be one value
;; made two ways.
(define inc-fx (subr (conv fx) pure (int) int) (lambda (x) (+ x 1)))
(define ignore (allof (subr pure ((subr pure (int) int)) int)
                      (subr pure ((subr (conv fx) pure (int) int)) int))
  (lambda (f) 1))
(ignore inc-fx)
