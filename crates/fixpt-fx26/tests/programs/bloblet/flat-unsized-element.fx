;; ! a flat array's element has a length of its own
;; An array's elements are all of one size, known (TODO.md §77).
(define-type r (blobref (bloblet (fields) @b) (arrayof (arrayof f64 finite) 3)))
