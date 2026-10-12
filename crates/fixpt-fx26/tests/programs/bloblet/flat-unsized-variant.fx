;; ! a flat sum's variant has a length of its own
;; A flat sum is as wide as its widest variant, so each has a size (TODO.md
;; §77).
(define-type r (blobref (bloblet (fields) @b) (sumof (none u32) (some (arrayof f64 finite)))))
