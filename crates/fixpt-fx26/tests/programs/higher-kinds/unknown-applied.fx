;; ! `queueuof` is not a description function
;; A name applied in a type that is none: said by name, not "expected a
;; type" (a typo in the user's okasaki.fx).
(define-type sig
  (moduleof (abs queueof (=> (type) type))
            (val empty (poly ((a type)) (queueuof a)))))
