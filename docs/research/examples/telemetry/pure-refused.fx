;;; EXPECTED TO FAIL: a procedure that says `pure` may not read a clock.
;;; MOCK prelude as in time-fib.fx.
(define-effect observes (maxeff (read @telemetry) (write @telemetry)))
(define real-time-ns (subr observes () nat)
  (let ((ticks (the (ref int @telemetry) (new 0))))
    (lambda () (begin (set ticks (+ (get ticks) 1000)) (confirm-nat (get ticks) (n n) 0)))))

;; A "hash" seeded from the clock claims to be pure: refused.
(define seeded (subr pure (int) int)
  (lambda (x) (+ x (real-time-ns))))
