;;; Refused: without `term-up`, a closed term is not a term in context,
;;; since a generative family is invariant.
(define-type (maybe (v type)) (oneof (none unit) (some v)))
(define-generative (term (v type))
  (oneof (var v)
         (app (tupof (f (term v)) (x (term v))))
         (lam (term (maybe v)))))
;; \x. x, closed.
(define id-term (term void)
  (up-term (one lam (up-term (one var (one none #u))))))
(define in-context (term int) id-term)                     ; refused: no term-up
