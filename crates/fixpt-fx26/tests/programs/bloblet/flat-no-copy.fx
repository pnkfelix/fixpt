;; ! only a scalar's bytes are read or written, and this points to a (productof (x f64) (y f64))
;; Nothing larger than a word is read out as a value: a flat product is
;; reached through its fields, each a blobref.
(define-type o (bloblet (fields) @b))
(define b o (make-bloblet 16))
(blobref-get (the (blobref o (productof (x f64) (y f64))) (blobref-at b 0)))
