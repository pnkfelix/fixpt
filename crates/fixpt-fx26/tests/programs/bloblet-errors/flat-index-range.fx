;; ! blobref-index: out of range
;; A flat array's index is checked against its length when it is taken.
(define-type o (bloblet (fields) @b))
(define b o (make-bloblet 24))
(define arr (blobref o (arrayof f64 3)) (blobref-at b 0))
(blobref-index arr 3)
