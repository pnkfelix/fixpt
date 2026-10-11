;; ! has no `z` laid out
;; A blobref to a flat product has its fields, and no others.
(define-type o (bloblet (fields) @b))
(define b o (make-bloblet 16))
(define p (blobref o (productof (x f64) (y f64))) (blobref-at b 0))
(extract p z)
