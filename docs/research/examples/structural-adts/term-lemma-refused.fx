;;; Refused, as it must be: the coercion for `maybe` turns `some x` into
;;; `none`, so it is no identity, and the lemma proves nothing ("each arm
;;; rebuilds its own tag").
(define-type (maybe (v type)) (oneof (none unit) (some v)))
(define-generative (term (v type))
  (oneof (var v)
         (app (tupof (f (term v)) (x (term v))))
         (lam (term (maybe v)))))
(define* term-up (proves (poly ((a type) (b type)) (<= (term a) (term b)) (<= a b)))
  (lambda (f t)
    (up-term (tagcase (down-term t)
               (var x (one var (f x)))
               (app (g x) (one app (tup (f (term-up f g)) (x (term-up f x)))))
               (lam body
                 (one lam (term-up (lambda ((m (maybe a)))
                                     (the (maybe b)
                                       (tagcase m
                                         (none u (one none u))
                                         (some x (one none #u)))))
                                   body)))))))
