;; ! a flat
;; As a blobref made by a step (`blobref+`): from a byte of a 16-byte suffix
;; to a pair of `f64`s, at byte 8, which runs past its end (TODO.md §77).
(define-type o (bloblet (fields) @b))
(define b o (make-bloblet 16))
(define at (blobref o u32) (blobref-at b 0))
(define pair (blobref o (productof (x f64) (y f64))) (blobref+ at 8))
