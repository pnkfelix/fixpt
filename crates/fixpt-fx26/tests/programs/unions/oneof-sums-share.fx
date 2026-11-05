;; ! a `oneof`'s sums must have no tag in common: a a and a b both have `x`
;; Two sums sharing a tag: no test tells a value tagged `x` as one or the other.
(define-type a (sumof (x int) (y int)))
(define-type b (sumof (x int) (z bool)))
(define f (subr pure ((oneof a b)) int) (lambda (v) 0))
