; Rejected: a bytevector made at a region that ends may not outlive it, as
; an array may not (TODO.md §84).
(define leak (subr (alloc @heap) () int)
  (lambda ()
    (bytevector-length (letregion r (the (bytevectorof r) (make-bytevector 3 (int->u8 1)))))))
