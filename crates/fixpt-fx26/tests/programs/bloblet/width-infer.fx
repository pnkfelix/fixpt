;; => (7 . #t)
;; A procedure polymorphic in a bloblet's first field, given one of more:
;; the field's type found from the fields the pattern lists.
(define first (poly ((a type)) (subr (read @b) ((bloblet (fields a) @b)) a))
  (plambda ((a type)) (lambda (b) (bloblet-ref b 0))))
(define b (bloblet (fields int bool) @b) (make-bloblet 0 7 #t))
(define c (bloblet (fields bool int) @b) (make-bloblet 0 #t 1))
(cons (first b) (first c))
