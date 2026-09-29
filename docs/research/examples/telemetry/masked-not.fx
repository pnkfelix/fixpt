;;; Masking removes what a body does to its own region, but never
;;; @telemetry: `local-work` is pure, `timed-local-work` is not, although
;;; the clock readings never leave it except as a difference.
;;; MOCK prelude as in time-fib.fx.
(define-effect observes (maxeff (read @telemetry) (write @telemetry)))
(define real-time-ns (subr observes () nat)
  (let ((ticks (the (ref int @telemetry) (new 0))))
    (lambda () (begin (set ticks (+ (get ticks) 1000)) (confirm-nat (get ticks) (n n) 0)))))

;; A counter in a region of its own: masked, so pure.
(define local-work (subr pure (int) int)
  (lambda (n)
    (letregion r
      (let ((c (the (ref int r) (new 0))))
        (begin (set c (+ (get c) n)) (get c))))))

;; The same, with the clock read: @telemetry is a constant, never masked.
(define* timed-local-work (subr observes (int) int)
  (lambda (n)
    (let* ((t0 (real-time-ns)) (v (local-work n)) (t1 (real-time-ns)))
      (- t1 t0))))

(timed-local-work 7)   ; 1000 with the stub clock
