;; => 9
;; A blobref is covariant in its owner: one into a bloblet of more fields
;; is taken where one into a bloblet of fewer is wanted.
(define-type one (bloblet (fields int) @b))
(define-type two (bloblet (fields int bool) @b))
(define first (subr (read @b) ((blobref one f64)) int)
  (lambda (r) (bloblet-ref (blobref-owner r) 0)))
(define b two (make-bloblet 8 9 #t))
(first (the (blobref two f64) (blobref-at b 0)))
