;; ! tagcase: no arm for this flat sum's tag
;; A flat sum's tag says what its bytes say: here, field 0 of the owner,
;; a label the sum does not have; no arm takes it.
(define-type o (bloblet (fields symbol) @b))
(define b o (make-bloblet 16 'z))
(define r (blobref o (sumof (a f64) (b i32))) (blobref-at b 0))
(tagcase r (a x 0) (b y 1))
