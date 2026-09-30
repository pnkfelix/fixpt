;;; CHUDNOVSKY -- Compute digits of PI using a straightforward
;;; implementation of the Chudnovsky brothers algorithm; see
;;; http://www.craig-wood.com/nick/articles/pi-chudnovsky/
;;;
;;; From Larceny's R7RS benchmarks
;;; (test/Benchmarking/R7RS/src/chudnovsky.scm), ported to FX-26. Larceny's
;;; input: 500 iterations of (pies 50 500 50). Answer: pi to 50, 100, ...
;;; 500 digits, ten integers:
;;; (314159265358979323846264338327950288419716939937510
;;;  31415926535897932384626433832795028841971693993751058209749445923078
;;;  164062862089986280348253421170679 ... 3141592653...489122793818301194912).
;;;
;;; The one float: the number of terms, (exact (floor (+ 2 (/ digits
;;; 14.181647462)))), is computed exactly, as 2 + digits * 10^9 quotient
;;; 14181647462; the two agree for every count of digits the benchmark
;;; asks (5, 9, 12, 16, 19, 23, 26, 30, 33, 37 terms for 50 to 500).
;;; FX-26 has no `exact-integer-sqrt` or `expt`: the file carries them, on
;;; `int` (exact, of any size). `integer-sqrt` is Newton's method from a
;;; power of two within a factor of two of the root, found by repeated
;;; squaring; `expt` is by squaring, and `(expt -1 b)` a test of `b`'s
;;; parity. `*` takes two operands: a product of three is two products.
;;; `ch-C^3`, 640320^3, is a fixnum still.

(define ch-A int 13591409)
(define ch-B int 545140134)
(define ch-C int 640320)
(define ch-C^3 int (* ch-C (* ch-C ch-C)))
(define ch-D int 12)

;; Exponentiation by squaring, for n >= 0.
(define* expt (subr (maxeff spin) (int int) int)
  (lambda (b n)
    (if (= n 0)
        1
        (let ((h (expt (* b b) (quotient n 2))))
          (if (= (modulo n 2) 0) h (* b h))))))

(define-type ints (listof int @heap))

(define* ch-split (subr (maxeff (alloc @heap) (read @heap) spin) (int int) ints)
  (lambda (a b)
    (if (= 1 (- b a))
        (let ((g (* (- (* 6 b) 5) (* (- (* 2 b) 1) (- (* 6 b) 1)))))
          (list g
                (quotient (* ch-C^3 (expt b 3)) 24)
                (* (if (= (modulo b 2) 0) 1 -1) (* g (+ (* b ch-B) ch-A)))))
        (let* ((mid (quotient (+ a b) 2))
               (gpq1 (ch-split a mid))
               (gpq2 (ch-split mid b))
               (g1 (car gpq1)) (p1 (car (cdr gpq1))) (q1 (car (cdr (cdr gpq1))))
               (g2 (car gpq2)) (p2 (car (cdr gpq2))) (q2 (car (cdr (cdr gpq2)))))
          (list (* g1 g2)
                (* p1 p2)
                (+ (* q1 p2) (* q2 g1)))))))

;; The powers 2^(2^j), j = 0, 1, ..., while their square is at most x, the
;; largest first.
(define* powers-under (subr (maxeff (alloc @heap) spin) (int int ints) ints)
  (lambda (x p ps)
    (if (> (* p p) x) ps (powers-under x (* p p) (cons p ps)))))

;; The largest power of two g with g*g <= x (x >= 1), from the powers.
(define* power-under (subr (maxeff (read @heap) spin) (int int ints) int)
  (lambda (x g ps)
    (if (null? ps)
        g
        (let ((h (* g (car ps))))
          (power-under x (if (> (* h h) x) g h) (cdr ps))))))

;; Newton's method, from g >= floor(sqrt(x)): floor(sqrt(x)).
(define* newton-sqrt (subr (maxeff spin) (int int) int)
  (lambda (x g)
    (let ((g2 (quotient (+ g (quotient x g)) 2)))
      (if (>= g2 g) g (newton-sqrt x g2)))))

;; exact-integer-sqrt's root, for x >= 0.
(define* integer-sqrt (subr (maxeff (alloc @heap) (read @heap) spin) (int) int)
  (lambda (x)
    (if (< x 2)
        x
        (newton-sqrt x (* 2 (power-under x 1 (powers-under x 2 nil)))))))

;; (exact (floor (+ 2 (/ digits 14.181647462)))), exactly.
(define num-terms-of (subr pure (int) int)
  (lambda (digits) (+ 2 (quotient (* digits 1000000000) 14181647462))))

(define* pi (subr (maxeff (alloc @heap) (read @heap) spin) (int) int)
  (lambda (digits)
    (let* ((num-terms (num-terms-of digits))
           (sqrt-C (integer-sqrt (* ch-C (expt 100 digits)))))
      (let* ((gpq (ch-split 0 num-terms))
             (g (car gpq)) (p (car (cdr gpq))) (q (car (cdr (cdr gpq)))))
        (quotient (* p (* ch-C sqrt-C)) (* ch-D (+ q (* p ch-A))))))))

(define* pies (subr (maxeff (alloc @heap) (read @heap) spin) (int int int) ints)
  (lambda (n m s)
    (if (< m n)
        nil
        (cons (pi n)
              (pies (+ n s) m s)))))

;; The inputs, where no compiler can fold them (Larceny's `hide`): globals,
;; which a later definition may replace.
(define input1 int 50)
(define input2 int 500)
(define input3 int 50)
(define iterations int 500)

(define* run (subr (maxeff (read @heap) (alloc @heap) spin) (int ints) ints)
  (lambda (i result) (if (= i 0) result (run (- i 1) (pies input1 input2 input3)))))
(run iterations nil)
