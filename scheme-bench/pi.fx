;;; PI -- Compute PI using bignums.
;;;
;;; See http://mathworld.wolfram.com/Pi.html for the various algorithms.
;;;
;;; From Larceny's R7RS benchmarks (test/Benchmarking/R7RS/src/pi.scm),
;;; ported to FX-26. Larceny's input: 2 iterations of (pies 50 500 50).
;;; Answer: ten lists (b2 bs-b2 b4-b2), one for each of 50, 100, ... 500
;;; digits, b2 pi to that many digits by the quadratic Borwein method:
;;; ((314159265358979323846264338327950288419716939937507 -54 124)
;;;  (31415926535897932384626433832795028841971693993751058209749445923078
;;;   164062862089986280348253421170673 -51 -417) ... ( ... -76 -3726)).
;;;
;;; FX-26 has no `exact-integer-sqrt`, `expt` or `square`: the file carries
;;; them, on `int` (exact, of any size). `exact-integer-sqrt`'s root is
;;; `isqrt`, Newton's method from a power of two within a factor of two of
;;; the root, found by repeated squaring. `expt` is by squaring. The named
;;; `let` loops are local `letrec` loops.

;; Exponentiation by squaring, for n >= 0.
(define* expt (subr (maxeff spin) (int int) int)
  (lambda (b n)
    (if (= n 0)
        1
        (let ((h (expt (* b b) (quotient n 2))))
          (if (= (modulo n 2) 0) h (* b h))))))

(define square (subr pure (int) int) (lambda (x) (* x x)))

;; The powers 2^(2^j), j = 0, 1, ..., while their square is at most x, the
;; largest first.
(define-type ints (listof int @heap))
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
(define* isqrt (subr (maxeff (alloc @heap) (read @heap) spin)
                    (int) int)
  (lambda (x)
    (if (< x 2)
        x
        (newton-sqrt x (* 2 (power-under x 1 (powers-under x 2 nil)))))))

(define* square-root (subr (maxeff (alloc @heap) (read @heap) spin)
                          (int) int)
  (lambda (x) (isqrt x)))

(define* quartic-root (subr (maxeff (alloc @heap) (read @heap) spin)
                           (int) int)
  (lambda (x) (square-root (square-root x))))

;;; Compute pi using the 'brent-salamin' method.

(define* pi-brent-salamin
  (subr (maxeff (alloc @heap) (read @heap) spin)
        (int) int)
  (lambda (nb-digits)
    (let ((one (expt 10 nb-digits)))
      (letrec ((loop (subr (maxeff (alloc @heap) (read @heap) spin
                                   (read (globals square square-root isqrt
                                                  newton-sqrt power-under powers-under)))
                           (int int int int) int)
                 (lambda (a b t x)
                   (if (= a b)
                       (quotient (square (+ a b)) (* 4 t))
                       (let ((new-a (quotient (+ a b) 2)))
                         (loop new-a
                               (square-root (* a b))
                               (- t
                                  (quotient
                                   (* x (square (- new-a a)))
                                   one))
                               (* 2 x)))))))
        (loop one
              (square-root (quotient (square one) 2))
              (quotient one 4)
              1)))))

;;; Compute pi using the quadratically converging 'borwein' method.

(define* pi-borwein2
  (subr (maxeff (alloc @heap) (read @heap) spin)
        (int) int)
  (lambda (nb-digits)
    (let* ((one (expt 10 nb-digits))
           (one^2 (square one))
           (one^4 (square one^2))
           (sqrt2 (square-root (* one^2 2)))
           (qurt2 (quartic-root (* one^4 2))))
      (letrec ((loop (subr (maxeff (alloc @heap) (read @heap) spin
                                   (read (globals square-root isqrt
                                                  newton-sqrt power-under powers-under)))
                           (int int int) int)
                 (lambda (x y p)
                   (let ((new-p (quotient (* p (+ x one))
                                          (+ y one))))
                     (if (= x one)
                         new-p
                         (let ((sqrt-x (square-root (* one x))))
                           (loop (quotient
                                  (* one (+ x one))
                                  (* 2 sqrt-x))
                                 (quotient
                                  (* one (+ (* x y) one^2))
                                  (* (+ y one) sqrt-x))
                                 new-p)))))))
        (loop (quotient
               (* one (+ sqrt2 one))
               (* 2 qurt2))
              qurt2
              (+ (* 2 one) sqrt2))))))

;;; Compute pi using the quartically converging 'borwein' method.

(define* pi-borwein4
  (subr (maxeff (alloc @heap) (read @heap) spin)
        (int) int)
  (lambda (nb-digits)
    (let* ((one (expt 10 nb-digits))
           (one^2 (square one))
           (one^4 (square one^2))
           (sqrt2 (square-root (* one^2 2))))
      (letrec ((loop (subr (maxeff (alloc @heap) (read @heap) spin
                                   (read (globals square quartic-root square-root isqrt
                                                  newton-sqrt power-under powers-under)))
                           (int int int) int)
                 (lambda (y a x)
                   (if (= y 0)
                       (quotient one^2 a)
                       (let* ((t1 (quartic-root (- one^4 (square (square y)))))
                              (t2 (quotient
                                   (* one (- one t1))
                                   (+ one t1)))
                              (t3 (quotient
                                   (square (quotient (square (+ one t2)) one))
                                   one))
                              (t4 (+ one
                                     (+ t2
                                        (quotient (square t2) one)))))
                         (loop t2
                               (quotient
                                (- (* t3 a) (* x (* t2 t4)))
                                one)
                               (* 4 x)))))))
        (loop (- sqrt2 one)
              (- (* 6 one) (* 4 sqrt2))
              8)))))

;;; Try it.

(define-type results (listof ints @heap))

(define* pies (subr (maxeff (alloc @heap) (read @heap) spin) (int int int) results)
  (lambda (n m s)
    (if (< m n)
        nil
        (let ((bs (pi-brent-salamin n))
              (b2 (pi-borwein2 n))
              (b4 (pi-borwein4 n)))
          (cons (list b2 (- bs b2) (- b4 b2))
                (pies (+ n s) m s))))))

;; The inputs, where no compiler can fold them (Larceny's `hide`): globals,
;; which a later definition may replace.
(define input1 int 50)
(define input2 int 500)
(define input3 int 50)
(define iterations int 2)

(define* run (subr (maxeff (read @heap) (alloc @heap) spin) (int results) results)
  (lambda (i result) (if (= i 0) result (run (- i 1) (pies input1 input2 input3)))))
(run iterations nil)
