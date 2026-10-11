;; ! a blobref to a flat sum is expected here
;; Only a blobref to a flat sum is made a variant.
(define-type o (bloblet (fields symbol) @b))
(define b o (make-bloblet 16 'a))
(blobref-variant! (the (blobref o f64) (blobref-at b 0)) 'a)
