;;; Two `letrec` procedures only called, so lambda-lifted: `up` takes `n`
;;; and `bump`'s `base` before its own arguments, and still loops; `f`
;;; makes no closure.
(define* f (subr spin (int int) int)
  (lambda (base n)
    (letrec ((up (subr spin (int int) int)
               (lambda (i acc) (if (= i n) acc (up (+ i 1) (+ acc (bump i))))))
             (bump (subr pure (int) int) (lambda (i) (+ i base))))
      (+ 1 (up 0 0)))))
(f 10 5)
