;; ! a flat is `f64`
;; A flat product's members are flats.
(define-type t (blobref (bloblet (fields) @b) (tupof (x f64) (s (listof int @b)))))
