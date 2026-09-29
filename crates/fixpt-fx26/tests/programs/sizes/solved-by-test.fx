; Accepted: past `(null? xs)`, the facts show m - 1 ≥ 0, so `head` may take
; the list.
(define head (poly ((t type) (n size)) (subr pure ((nlist t (+ n 1))) t))
  (lambda (xs) (car xs)))
(define g (poly ((m size)) (subr (read (globals head)) ((nlist int m)) int))
  (plambda ((m size)) (lambda (xs) (if (null? xs) 0 (head xs)))))
(g (the (nlist int finite) (cons 5 nil)))
