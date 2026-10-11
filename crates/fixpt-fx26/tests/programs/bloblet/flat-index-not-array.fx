;; ! a blobref to a flat array is expected here
;; Only a blobref to a flat array is indexed.
(define-type o (bloblet (fields) @b))
(define b o (make-bloblet 16))
(blobref-index (the (blobref o f64) (blobref-at b 0)) 0)
