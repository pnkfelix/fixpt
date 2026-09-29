;;; Timing `fib 25` by hand: two clock reads around a pure call.
;;; MOCK: `@telemetry`, `observes`, `real-time-ns` and `black-box` are the
;;; proposal in docs/research/telemetry.md, stubbed in today's FX-26. The
;;; stub clock is a counter at @telemetry that ticks 1000 "ns" per read, so
;;; the effect checking is real and the numbers are not.
(define-effect observes (maxeff (read @telemetry) (write @telemetry)))
(define real-time-ns (subr observes () nat)
  (let ((ticks (the (ref int @telemetry) (new 0))))
    (lambda () (begin (set ticks (+ (get ticks) 1000)) (confirm-nat (get ticks) (n n) 0)))))
(define sink (ref int @telemetry) (new 0))
(define* black-box (poly ((t type)) (subr observes (t) t))
  (plambda ((t type)) (lambda ((x t)) (begin (set sink 0) x))))

;; The workload: pure, and proved to end (it counts down under (< n 2)).
(define fib (subr pure (int) int)
  (letrec ((fib (subr pure (int) int)
             (lambda (n) (if (< n 2) n (+ (fib (- n 1)) (fib (- n 2)))))))
    fib))

;; The measurement: its type must say `observes`, since its result is not
;; a function of its argument. But `(fib n)` is pure, so a compiler may
;; still compute it before t0 or after t1: nothing pins it in the window.
(define* time-fib (subr observes (int) (productof (value int) (ns int)))
  (lambda (n)
    (let* ((t0 (real-time-ns))
           (v  (fib n))
           (t1 (real-time-ns)))
      (product (value v) (ns (- t1 t0))))))

;; Pinned: `(black-box n)` is ordered after t0, `(black-box (fib …))`
;; before t1, and fib's call depends on the one and feeds the other.
(define* time-fib-pinned (subr observes (int) (productof (value int) (ns int)))
  (lambda (n)
    (let* ((t0 (real-time-ns))
           (v  (black-box (fib (black-box n))))
           (t1 (real-time-ns)))
      (product (value v) (ns (- t1 t0))))))

(+ (extract (time-fib 25) value) (extract (time-fib-pinned 25) ns))   ; 75025 + 1000
