;;; A benchmark loop that a compiler using effect summaries could empty,
;;; and the same loop pinned with `black-box` (Chez Scheme 10's name).
;;; MOCK: `black-box` is the proposal, stubbed as an identity that writes
;;; a counter at @telemetry, so it has the proposed type and effect.
(define-effect observes (maxeff (read @telemetry) (write @telemetry)))
;; (A polymorphic value must be pure, so the stub's cell is a global of
;; its own, and `define*` adds `(read (globals sink))` to its type.)
(define sink (ref int @telemetry) (new 0))
(define* black-box (poly ((t type)) (subr observes (t) t))
  (plambda ((t type)) (lambda ((x t)) (begin (set sink 0) x))))

(define fib (subr pure (int) int)
  (letrec ((fib (subr pure (int) int)
             (lambda (n) (if (< n 2) n (+ (fib (- n 1)) (fib (- n 2)))))))
    fib))

;; 1. `(fib 20)` is pure and ends, and its value is unused: summary 0,
;;    so a compiler may drop it, and the loop does nothing k times.
(define* loop-dropped (subr spin (int) int)
  (lambda (k) (if (= k 0) 0 (begin (fib 20) (loop-dropped (- k 1))))))

;; 2. The value is consumed, but `(fib 20)` is loop-invariant and pure:
;;    a compiler may compute it once, before the loop.
(define* loop-hoisted (subr (maxeff observes spin) (int) int)
  (lambda (k) (if (= k 0) 0 (begin (black-box (fib 20)) (loop-hoisted (- k 1))))))

;; 3. Input and output both through `black-box`: each iteration's
;;    argument is a fresh observation (summary 2, never shared or hoisted),
;;    and its result is used. fib really runs k times.
(define* loop-pinned (subr (maxeff observes spin) (int) int)
  (lambda (k) (if (= k 0) 0 (begin (black-box (fib (black-box 20))) (loop-pinned (- k 1))))))

(loop-pinned 10)
