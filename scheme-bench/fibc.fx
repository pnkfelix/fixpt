;;; FIBC -- FIB using first-class continuations, written by Kent Dybvig
;;; fib with peano arithmetic (using numbers) with call/cc
;;;
;;; From Larceny's R7RS benchmarks (test/Benchmarking/R7RS/src/fibc.scm),
;;; ported to FX-26. Larceny's input: 10 iterations of (fibc 30 (lambda (n) n)).
;;; Answer: 832040.
;;;
;;; `call-with-current-continuation` is `cwcc`, its continuations in the
;;; region `@k`. A continuation, which never returns, and the initial
;;; identity are both a `kont`: `void` is a subtype of `int`. `(zero? n)`
;;; is `(= n 0)`.

(define-type kont (subr (goto @k) (int) int))

(define succ (subr pure (int) int) (lambda (n) (+ n 1)))
(define pred (subr pure (int) int) (lambda (n) (- n 1)))

(define* addc (subr (maxeff (goto @k) spin) (int int kont) int)
  (lambda (x y k)
    (if (= y 0)
        (k x)
        (addc (succ x) (pred y) k))))

(define* fibc (subr (maxeff (goto @k) (comefrom @k) spin) (int kont) int)
  (lambda (x c)
    (if (= x 0)
        (c 0)
        (if (= (pred x) 0)
            (c 1)
            (addc (cwcc (lambda ((c (subr (goto @k) (int) void))) (fibc (pred x) c)))
                  (cwcc (lambda ((c (subr (goto @k) (int) void))) (fibc (pred (pred x)) c)))
                  c)))))

;; The inputs, where no compiler can fold them (Larceny's `hide`): globals,
;; which a later definition may replace.
(define input int 30)
(define identity kont (lambda (n) n))
(define iterations int 10)

(define* run (subr (maxeff (goto @k) (comefrom @k) spin) (int int) int)
  (lambda (i result) (if (= i 0) result (run (- i 1) (fibc input identity)))))
(run iterations 0)
