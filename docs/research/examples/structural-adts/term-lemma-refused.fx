;;; Refused, as it must be: the coercion for `maybe` turns `some x` into
;;; `none`, so it is no identity, and the lemma proves nothing ("each arm
;;; rebuilds its own tag").
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
                                         (some x (sum none #u)))))
                                   body)))))))
