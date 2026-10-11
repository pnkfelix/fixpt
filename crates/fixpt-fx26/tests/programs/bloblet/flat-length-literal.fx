;; ! a flat array's length is a literal, for now
;; A flat array's length is a literal.
(define-type t (poly ((n size)) (blobref (bloblet (fields) @b) (arrayof f64 n))))
