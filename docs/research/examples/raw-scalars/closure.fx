;;; INTEGRATE (closure) -- Simpson's rule over an integrand given as a
;;; procedure value: 4/(1+x^2) over [0, 1], which is pi, with `n`
;;; intervals, `reps` times; `w` the weight, 4 and 2 in turn.
;;; The integrand, a closure over
;;; an `f64` (the 4.), reaches `simpson` as an argument.

(define four f64 4.)

(define* make-integrand (subr pure (f64) (subr pure (f64) f64))
  (lambda (k) (lambda (x) (f64/ k (f64+ 1. (f64* x x))))))

(define* simpson-loop
  (subr (maxeff spin) ((subr pure (f64) f64) f64 f64 int int f64 f64) f64)
  (lambda (f a h i n w acc)
    (if (>= i n)
        acc
        (let ((y (f (f64+ a (f64* h (int->f64 i))))))
          (simpson-loop f a h (+ i 1) n (f64- 6. w)
                        (f64+ acc (f64* w y)))))))

(define* simpson
  (subr (maxeff spin (read (globals simpson-loop)))
        ((subr pure (f64) f64) f64 f64 int) f64)
  (lambda (f a b n)
    (let ((h (f64/ (f64- b a) (int->f64 n))))
      (f64/ (f64* h (simpson-loop f a h 1 n 4. (f64+ (f a) (f b)))) 3.))))

(define* run
  (subr (maxeff spin (read (globals simpson simpson-loop make-integrand four))) (int int f64) f64)
  (lambda (reps n acc)
    (if (= reps 0)
        acc
        (run (- reps 1) n (f64+ acc (simpson (make-integrand four) 0. 1. n))))))

(define reps int 20)
(f64->string (run reps 200000 0.))
