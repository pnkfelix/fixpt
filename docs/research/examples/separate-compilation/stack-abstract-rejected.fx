;;; Rejected, as it should be: a client written for any s cannot take the
;;; stack apart as a list, though the one it is given is one.

;;; ---- stack.fx ----
(define-type (stack-ops (s type))
  (productof (empty s)
             (push (subr pure (int s) s))
             (top  (subr pure (s) int))))

;;; ---- client.fx ----
(define peek (poly ((s type)) (subr pure ((stack-ops s)) int))
  (plambda ((s type))
    (lambda (m) (car (extract m empty)))))
