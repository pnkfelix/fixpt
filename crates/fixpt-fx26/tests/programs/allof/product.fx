;; => ("a" "3")
;; An `allof` of products distributes over them (`logical-types.md` §8.5):
;; a product whose field `f` is the `allof` of the members' `f`s and whose
;; `n`, the same in each, is that. The `lambda` is checked against each.
(define-type ops (allof (productof (f (subr pure (int) int)) (n int))
                        (productof (f (subr pure (string) string)) (n int))))
(define p ops (product (f (lambda (x) x)) (n 3)))
(list ((extract p f) "a") (int->string ((extract p f) (extract p n))))
