;; ! blobref-index: out of range
;; An array that runs to the end of the suffix ends there: five `f64`s in
;; 40 bytes, so a sixth is out of range (TODO.md §77).
(define-type o (bloblet (fields) @b))
(define b o (make-bloblet 40))
(define arr (blobref o (arrayof f64 finite)) (blobref-at b 0))
(blobref-index arr 5)
