;;; CTAK -- A version of the TAK procedure that uses continuations.
;;;
;;; From Larceny's R7RS benchmarks (test/Benchmarking/R7RS/src/ctak.scm),
;;; ported to FX-26. Larceny's input: 1 iteration of (ctak 32 16 8).
;;; Answer: 9.
;;;
;;; `call-with-current-continuation` is `cwcc`, its continuations in the
;;; region `@k`. `ctak-aux` is defined first, since a definition sees only
;;; those before it.

(define-type kont (subr (goto @k) (int) void))

(define* ctak-aux (subr (maxeff (goto @k) (comefrom @k) spin) (kont int int int) int)
  (lambda (k x y z)
    (if (not (< y x))
        (k z)
        (cwcc
          (lambda ((k kont))
            (ctak-aux
             k
             (cwcc
               (lambda ((k kont)) (ctak-aux k (- x 1) y z)))
             (cwcc
               (lambda ((k kont)) (ctak-aux k (- y 1) z x)))
             (cwcc
               (lambda ((k kont)) (ctak-aux k (- z 1) x y)))))))))

(define* ctak (subr (maxeff (goto @k) (comefrom @k) spin) (int int int) int)
  (lambda (x y z)
    (cwcc
      (lambda ((k kont)) (ctak-aux k x y z)))))

;; The inputs, where no compiler can fold them (Larceny's `hide`): globals,
;; which a later definition may replace.
(define input1 int 32)
(define input2 int 16)
(define input3 int 8)
(define iterations int 1)

(define* run (subr (maxeff (goto @k) (comefrom @k) spin) (int int) int)
  (lambda (i result) (if (= i 0) result (run (- i 1) (ctak input1 input2 input3)))))
(run iterations 0)
