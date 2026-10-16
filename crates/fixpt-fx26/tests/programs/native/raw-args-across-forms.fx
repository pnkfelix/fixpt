;;; `f64`s passed raw to a procedure made native a form before (`TODO.md`
;;; §91): `sum-scaled`, compiled after `scale` was, passes it `x` and `k`
;;; raw; then `scale` is redefined, taking only `k` raw, and the same
;;; call, its guard failing, goes through the cell with both boxed; and
;;; `sum-again`, compiled after that, passes the new one `k` raw.
(define scale (->* (f64 f64) f64) (lambda (x k) (f64* x k)))
(define sum-scaled (->* (int f64) f64)
  (lambda (n acc) (if (= n 0) acc (sum-scaled (- n 1) (f64+ acc (scale (int->f64 n) .5))))))
(f64->int (sum-scaled 1000 0.))
(define scale (->* (f64 f64) f64) (lambda (x k) (if (f64< k 0.) x (f64* k 2.))))
(f64->int (sum-scaled 1000 0.))
(define sum-again (->* (int f64) f64)
  (lambda (n acc) (if (= n 0) acc (sum-again (- n 1) (f64+ acc (scale (int->f64 n) .25))))))
(f64->int (sum-again 1000 0.))
