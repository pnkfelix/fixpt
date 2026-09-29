;;; Larceny's `run-with-stats`, typed: a thunk runner polymorphic in the
;;; thunk's result type and effect, whose own effect adds `observes`.
;;; MOCK: `telemetry-begin` and `telemetry-end` are the proposal, stubbed
;;; over one fake counter at @telemetry; `run-with-stats` itself is written
;;; as the proposal says it would be, in FX-26 over those two.
(define-effect observes (maxeff (read @telemetry) (write @telemetry)))
(define-type run-stats
  (productof (real-ns nat) (cpu-ns nat) (gc-ns nat) (max-pause-ns nat)
             (words nat) (region-words nat) (copied nat)
             (minor nat) (major nat) (peak-words nat)))
(define now (ref int @telemetry) (new 0))
(define* telemetry-begin (subr observes () nat)
  (lambda () (begin (set now (+ (get now) 1)) (confirm-nat (get now) (n n) 0))))
(define* telemetry-end (subr observes (nat) run-stats)
  (lambda (token)
    (begin (set now (+ (get now) 1))
      (confirm-nat (- (get now) token) (d
        (product (real-ns d) (cpu-ns d) (gc-ns 0) (max-pause-ns 0) (words 0)
                 (region-words 0) (copied 0) (minor 0) (major 0) (peak-words 0)))
        (product (real-ns 0) (cpu-ns 0) (gc-ns 0) (max-pause-ns 0) (words 0)
                 (region-words 0) (copied 0) (minor 0) (major 0) (peak-words 0))))))

(define* run-with-stats
  (poly ((t type) (e effect))
    (subr (maxeff e observes) ((subr e () t)) (productof (value t) (stats run-stats))))
  (plambda ((t type) (e effect))
    (lambda ((thunk (subr e () t)))
      (let* ((k (telemetry-begin)) (v (thunk)) (s (telemetry-end k)))
        (product (value v) (stats s))))))

;; Two workloads: pure, and one that allocates and reads at @l.
(define fib (subr pure (int) int)
  (letrec ((fib (subr pure (int) int)
             (lambda (n) (if (< n 2) n (+ (fib (- n 1)) (fib (- n 2)))))))
    fib))
(define* iota (subr (maxeff (alloc @l) spin) (int (listof int @l)) (listof int @l))
  (lambda (n acc) (if (= n 0) acc (iota (- n 1) (cons n acc)))))
(define* add-up (subr (maxeff (read @l) spin) ((listof int @l) int) int)
  (lambda (xs acc) (if (null? xs) acc (add-up (cdr xs) (+ acc (car xs))))))

;; `(time (fib 25))` would expand to this; the call's effect is `observes`.
(define* time-fib (subr observes () (productof (value int) (stats run-stats)))
  (lambda () (run-with-stats (lambda () (fib 25)))))
;; The thunk's own effect shows through: `observes` plus alloc/read @l.
(define* time-list (subr (maxeff (alloc @l) (read @l) spin observes) ()
                         (productof (value int) (stats run-stats)))
  (lambda () (run-with-stats (lambda () (add-up (iota 100000 nil) 0)))))

(+ (extract (time-fib) value) (extract (time-list) value))   ; 75025 + 5000050000
