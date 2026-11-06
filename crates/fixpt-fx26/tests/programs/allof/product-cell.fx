;; ! an `allof`'s members differ at `c`
;; A cell's type is invariant: two products holding cells of different
;; types have no meet (F18), so this is refused where it is written.
(define-type bad (allof (productof (f (subr pure (int) int)) (c (ref int @heap)))
                        (productof (f (subr pure (string) string)) (c (ref string @heap)))))
1
