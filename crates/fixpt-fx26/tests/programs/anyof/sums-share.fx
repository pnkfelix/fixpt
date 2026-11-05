;; => (3 1 7)
;; Two sums sharing a tag, in an `anyof`: kept as written, and made one sum
;; where `tagcase` needs one, the shared tag's payload the union of its
;; payloads.
(define-type a (sumof (x int) (y int)))
(define-type b (sumof (x bool) (z bool)))
(define f (subr pure ((anyof a b)) int)
  (lambda (v) (tagcase v (x p (if (int? p) p (if p 1 0))) (y n n) (z q 7))))
(list (f (sum x 3)) (f (sum x #t)) (f (sum z #f)))
