;; ! a one is expected here, and this is a (bloblet (frozen int (ref int @b)) @b)
;; Refused: a frozen bloblet's forgotten field must be data, or the wider
;; type would be data with a mutable ref hidden in it.
(define-type one (bloblet (frozen int) @b))
(define b (bloblet (frozen int (ref int @b)) @b)
  (bloblet-freeze (the (bloblet (fields int (ref int @b)) @b) (make-bloblet 0 1 (new 2)))))
(define c one b)
