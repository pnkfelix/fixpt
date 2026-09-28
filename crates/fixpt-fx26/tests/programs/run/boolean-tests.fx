;;; Tests made of `and`, `or`, `not` and `if`, compiled as jumps (no
;;; boolean made): each part runs once, in order, and only as far as it
;;; must. `log` keeps a count of the parts that ran, as digits.
(define log (ref int @r) (new 0))
(define* note (subr (maxeff (read @r) (write @r)) (int bool) bool)
  (lambda (k b) (begin (set log (+ (* 10 (get log)) k)) b)))
(define* pick (subr (maxeff (read @r) (write @r)) (int int) int)
  (lambda (x y)
    (cond ((and (note 1 (< x 10)) (not (note 2 (= y 0)))) 1)
          ((or (note 3 (= x 3)) (note 4 (< y x))) 2)
          ((if (note 5 (> x 100)) (note 6 #f) (not (note 7 (= y 5)))) 3)
          (else 4))))
(define* run (subr (maxeff (read @r) (write @r)) (int int) int)
  (lambda (x y) (begin (set log 0) (let ((r (pick x y))) (+ (* 100000000 r) (get log))))))
(+ (run 3 4) (+ (run 3 0) (+ (run 20 30) (+ (run 200 30) (run 20 5)))))
