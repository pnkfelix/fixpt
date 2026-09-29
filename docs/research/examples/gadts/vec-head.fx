;;; FX-26 today: length-indexed lists are built in (`nlist`, sizes N5), so
;;; the safe `head` of the GADT papers is a signature: its argument has
;;; `n + 1` elements for some size `n`. Calling it on an empty list is
;;; refused (`vec-head-refused.fx`).
(define head (poly ((t type) (n size)) (subr pure ((nlist t (+ n 1))) t))
  (lambda (xs) (car xs)))
(define tail (poly ((t type) (n size)) (subr pure ((nlist t (+ n 1))) (nlist t n)))
  (lambda (xs) (cdr xs)))
(define three (nlist int 3) (cons 1 (cons 2 (cons 3 nil))))
(+ (head three) (head (tail three)))
