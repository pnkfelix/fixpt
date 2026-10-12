;; ! only a flat product's last part may be of a length not known
;; An array of a length not literal runs to the end of the suffix, so only
;; a product's last part may be one (TODO.md §77).
(define-type rec (productof (data (arrayof f64 finite)) (count u32)))
(define-type r (blobref (bloblet (fields) @b) rec))
