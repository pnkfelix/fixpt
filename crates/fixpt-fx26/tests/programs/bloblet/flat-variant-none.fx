;; ! has no variant `c`
;; A flat sum is made only one of its variants.
(define-type o (bloblet (fields symbol) @b))
(define b o (make-bloblet 16 'a))
(define r (blobref o (sumof (a f64) (b i32))) (blobref-at b 0))
(blobref-variant! r 'c)
