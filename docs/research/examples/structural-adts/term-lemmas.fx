;;; FX-26 today, generative: de Bruijn terms as a nested type (Bird and
;;; Paterson), `(term v)` over free variables `v`; under a `lam` the body
;;; has one more, `(maybe v)`. Expansive. The variance lemma hands itself a
;;; coercion for `maybe` that takes a sum apart and rebuilds it. With it,
;;; a closed term, a `(term void)`, is a term in any context: `void <= int`.
(define-type (maybe (v type)) (sumof (none unit) (some v)))
(define-generative (term (v type))
  (sumof (var v)
         (app (productof (f (term v)) (x (term v))))
         (lam (term (maybe v)))))
(define* term-up (proves (poly ((a type) (b type)) (<= (term a) (term b)) (<= a b)))
  (lambda (f t)
    (up-term (tagcase (down-term t)
               (var x (sum var (f x)))
               (app (g x) (sum app (product (f (term-up f g)) (x (term-up f x)))))
               (lam body
                 (sum lam (term-up (lambda ((m (maybe a)))
                                     (the (maybe b)
                                       (tagcase m
                                         (none u (sum none u))
                                         (some x (sum some (f x))))))
                                   body)))))))
;; \x. x, closed.
(define id-term (term void)
  (up-term (sum lam (up-term (sum var (sum none #u))))))
(define in-context (term int) id-term)                     ; by term-up, void <= int
