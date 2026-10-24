; Verified
;;; A logic function of an `int` result: `len`, called twice in the body,
;;; is the same term twice, the one the `ensures` names.
(define-type ints (listof int acyclic))
(define len (subr pure (ints) int)
  (letrec ((l (subr pure (ints) int) (lambda (xs) (if (null? xs) 0 (+ 1 (l (cdr xs)))))))
    l))
(define twice-len (subr (read (globals len)) ((xs ints)) int (ensures r (= r (* 2 (len xs)))))
  (lambda (xs) (+ (len xs) (len xs))))
(twice-len (list 1 2 3))
