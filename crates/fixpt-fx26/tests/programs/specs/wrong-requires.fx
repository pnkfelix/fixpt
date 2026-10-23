; Unverified
;;; A call that does not establish its callee's `requires`.
(define clamp (subr pure ((lo int) (hi int) (x int)) int
                (requires (<= lo hi))
                (ensures r (and (<= lo r) (<= r hi))))
  (lambda (lo hi x) (if (< x lo) lo (if (< hi x) hi x))))
(define f (subr (read (globals clamp)) ((x int)) int)
  (lambda (x) (clamp x 0 5)))
(f 3)
