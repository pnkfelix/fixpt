;; ! this `tagcase` has no arm for b
;; A `tagcase` on a flat sum covers its variants, or has an `else`.
(define-type o (bloblet (fields symbol) @b))
(define b o (make-bloblet 16 'a))
(define r (blobref o (sumof (a f64) (b i32))) (blobref-at b 0))
(tagcase r (a x 0))
