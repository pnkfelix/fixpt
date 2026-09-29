; Rejected: `head` wants a list of size n + 1, and an empty one would make
; n be -1 (found writing docs/research/gadts.md's examples; it ran and
; failed, "expected a pair").
(define head (poly ((t type) (n size)) (subr pure ((nlist t (+ n 1))) t))
  (lambda (xs) (car xs)))
(head (the (nlist int 0) nil))
