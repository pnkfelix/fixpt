;;; A generative type over a region that ends: used inside it, it is fine.
(define-generative (stack (t type) (r region)) (listof t r))
(define* f (subr pure () int)
  (lambda ()
    (letregion l
      (let ((s (the (stack int l) (up-stack (the (listof int l) (cons 1 nil))))))
        3))))
(f)
