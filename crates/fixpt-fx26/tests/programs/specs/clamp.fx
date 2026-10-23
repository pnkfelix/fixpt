; Verified
;;; A `requires`, assumed in the body: with `lo ≤ hi`, the result is
;;; between them.
(define clamp (subr pure ((lo int) (hi int) (x int)) int
                (requires (<= lo hi))
                (ensures r (and (<= lo r) (<= r hi))))
  (lambda (lo hi x) (if (< x lo) lo (if (< hi x) hi x))))
(clamp 0 10 42)
