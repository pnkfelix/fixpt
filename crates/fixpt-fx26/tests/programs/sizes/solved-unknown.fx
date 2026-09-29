; Rejected: a list of any size m may be empty, so `head` of it would make n
; be m - 1, which nothing here shows is no less than 0.
(define head (poly ((t type) (n size)) (subr pure ((nlist t (+ n 1))) t))
  (lambda (xs) (car xs)))
(define f (poly ((m size)) (subr (read (globals head)) ((nlist int m)) int))
  (plambda ((m size)) (lambda (xs) (head xs))))
