; Refused: the empty list has no head. (With the size given explicitly;
; left to inference, the same call is accepted: `vec-head-hole.fx`.)
(define head (poly ((t type) (n size)) (subr pure ((nlist t (+ n 1))) t))
  (lambda (xs) (car xs)))
((proj head int 0) (the (nlist int 0) nil))
