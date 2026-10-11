;; ! a (sumof (a (blobref o f64)) (b (blobref o i32))) has no tag `c`
;; An arm on a flat sum names one of its variants; it sees each as a
;; blobref to it.
(define-type o (bloblet (fields symbol) @b))
(define b o (make-bloblet 16 'a))
(define r (blobref o (sumof (a f64) (b i32))) (blobref-at b 0))
(tagcase r (c x 0) (else y 1))
