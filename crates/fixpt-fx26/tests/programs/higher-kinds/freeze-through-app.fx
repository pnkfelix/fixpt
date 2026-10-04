;; ! could still write its region's data
;; A description function applied, unseen, may keep a way to write what it
;; is given: a `letfreeze`'s value of type `(f (write r))` is refused.
(define g (poly ((f (=> effect type)))
            (subr pure ((poly ((r region)) (subr pure () (f (write r))))) int))
  (plambda ((f (=> effect type)))
    (lambda (mk) (begin (letfreeze r ((proj mk r))) 0))))
