;; ! flat sum: its tag names no field of its owner
;; A flat sum's tag indexes the owner's fields: one past them is refused
;; when it is read.
(define-type o (bloblet (fields symbol) @b))
(define b o (make-bloblet 16 'a))
(bloblet-set-byte! b 0 3)
(define r (blobref o (sumof (a f64) (b i32))) (blobref-at b 0))
(tagcase r (a x 0) (b y 1))
