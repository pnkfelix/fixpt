;; ! blobref-variant!: no field of the owner holds the label
;; Without a key, a flat sum's tag indexes the owner's fields: a variant
;; whose label none holds is not made.
(define-type o (bloblet (fields symbol) @b))
(define b o (make-bloblet 16 'a))
(define r (blobref o (sumof (a f64) (b i32))) (blobref-at b 0))
(blobref-variant! r 'b)
