;;; A procedure that builds at its caller's region, in its caller's place:
;;; `(r region p)` is a region that won't outlive `p`, so the caller must give
;;; a region bound inside the place (or the place itself).
(define build (poly ((p place) (r region p)) (subr (maxeff (alloc r) (alloc p)) ((place p) int) (listof int r)))
  (plambda ((p place) (r region p))
    (lambda ((h (place p)) (n int)) (rcons h n (rcons h (+ n 1) nil)))))
(define* use (subr pure (int) int)
  (lambda (n)
    (letrena a
      (letregion d
        (let ((xs ((proj build a d) a n)))
          (+ (car xs) (car (cdr xs))))))))
(use 20)
