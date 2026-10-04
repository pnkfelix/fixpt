;; ! takes 1 description(s), and has 2
;; A type constructor applied to as many descriptions as its kind says.
(define-type bad (dlambda ((f (=> (type) type))) (f int bool)))
