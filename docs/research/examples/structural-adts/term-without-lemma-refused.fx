;;; Refused: without `term-up`, a closed term is not a term in context,
;;; since a generative family is invariant.
(define-type (maybe (v type)) (sumof (none unit) (some v)))
(define-generative (term (v type))
  (sumof (var v)
         (app (productof (f (term v)) (x (term v))))
         (lam (term (maybe v)))))
;; \x. x, closed.
(define id-term (term void)
  (up-term (sum lam (up-term (sum var (sum none #u))))))
(define in-context (term int) id-term)                     ; refused: no term-up
