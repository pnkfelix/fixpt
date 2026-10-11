;; ! a one is expected here, and this is a (bloblet (fields int (ref int r)) @b)
;; Refused: a field forgotten that mentions another region. Widened, the
;; bloblet's type would not mention `r`, and it would leave `letrena r`
;; holding a ref into it after it is freed.
(define-type one (bloblet (fields int) @b))
(define keep (ref one @b) (new (make-bloblet 0 0)))
(letrena r
  (let ((x (the (ref int r) (new 1))))
    (set keep (the (bloblet (fields int (ref int r)) @b) (make-bloblet 0 2 x)))))
