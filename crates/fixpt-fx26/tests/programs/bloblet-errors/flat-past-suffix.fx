;; ! a flat
;; A new blobref's flat lies whole in the suffix (TODO.md §77): ten `f64`s
;; do not fit in 8 bytes, so a blobref that says they do is refused where
;; it is made, and what its type says of the array's length (10) holds
;; wherever one is.
(define-type o (bloblet (fields) @b))
(define b o (make-bloblet 8))
(define arr (blobref o (arrayof f64 10)) (blobref-at b 0))
