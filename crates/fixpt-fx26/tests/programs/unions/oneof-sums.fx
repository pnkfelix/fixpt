;; => (1 5 0)
;; Two sums with no tag in common are told apart by their tags: members of
;; one `oneof`, made one sum, which `tagcase` takes apart (logical-types.md
;; §8.5, the user's, 2026-11-05).
(define-type a (sumof (x int) (y int)))
(define-type c (sumof (z bool)))
(define-type ac (oneof a c nil))
(define f (subr pure (ac) int)
  (lambda (v) (if (null? v) 0 (tagcase v (x i i) (y j j) (z b (if b 1 2))))))
(list (f (sum z #t)) (f (sum y 5)) (f nil))
