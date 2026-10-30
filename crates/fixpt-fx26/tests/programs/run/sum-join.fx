; Branches of different sums join (`docs/fx26.md`, "Products and sums"):
; the sum of each's variants, a tag both have carrying its payloads' join,
; at an `if` and among a `tagcase`'s arms, with no type expected.
(define pick (lambda ((c bool)) (if c (sum #:a 1) (sum #:b "x"))))
(define which (subr pure ((sumof (#:a int) (#:b string))) int)
  (lambda (s) (tagcase s (#:a n n) (#:b t 10))))
(define nested
  (lambda ((k int))
    (tagcase (the (sumof (x unit) (y unit)) (if (= k 0) (sum x #u) (sum y #u)))
      (#:x u (sum #:p (sum #:q 1)))
      (#:y u (sum #:p (sum #:r #t))))))
(define deep (subr pure ((sumof (#:p (sumof (#:q int) (#:r bool))))) int)
  (lambda (s) (tagcase s (#:p v (tagcase v (#:q n n) (#:r b 100))))))
(+ (+ (which (pick #t)) (which (pick #f))) (+ (deep (nested 0)) (deep (nested 1))))
