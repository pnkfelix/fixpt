;;; QUICKSORT -- This is probably from Lars Hansen's MS thesis.
;;; The quick-1 benchmark.  (Figure 35, page 132.)
;;;
;;; From Larceny's R7RS benchmarks (test/Benchmarking/R7RS/src/quicksort.scm),
;;; ported to FX-26. Larceny's input: 2500 iterations of (quick-1 (a copy
;;; of v) less?), v a vector of 10000 random integers below 1000000.
;;; Answer: #t (the sorted copy is in order, Larceny's check).
;;;
;;; Vectors are arrays; `(vector-map values v)` is a copy, written out.
;;; The random vector is made once, before the iterations, as in Larceny.
;;;
;;; Its generator is Pierre L'Ecuyer's combined multiple recursive
;;; generator (MRG32k3a), which Larceny's file runs in flonums, "using no
;;; conversions between flonums and fixnums". Every flonum it computes is
;;; an integer below 2^53, so here it runs in integers, the same
;;; computation exactly; `random` scales its result, `(* norm x)` with
;;; `norm` = 1/(m1 + 1) to within 2^-53, by a quotient by m1 + 1. For
;;; this benchmark's 10000 draws below 1000000, that gives Larceny's
;;; values, every one (checked against IEEE doubles). FX-26 has no
;;; flonums; the sort itself never used them.

;;; Hansen's original code for this benchmark used Larceny's
;;; predefined random procedure.  When Marc Feeley modified
;;; Hansen's benchmark for the Gambit benchmark suite, however,
;;; he added a specific random number generator taken from an
;;; article in CACM.  Feeley's generator used bignums, and was
;;; extremely slow, causing the Gambit version of this benchmark
;;; to spend nearly all of its time generating the random numbers.
;;; For a benchmark called quicksort to become a bignum benchmark
;;; was very misleading, so Clinger left Feeley's version of this
;;; benchmark out of the Larceny benchmark suite.
;;;
;;; The following random number generator is much better and
;;; faster than the one used in the Gambit benchmark.  See
;;;
;;; http://srfi.schemers.org/srfi-27/mail-archive/msg00000.html
;;; http://www.math.purdue.edu/~lucier/random/random.scm

(define-type vec (arrayof int @heap))
(define-type less (subr pure (int int) bool))
(define-effect vecs (maxeff (read @heap) (write @heap) (alloc @heap) spin))

(define* partition (subr vecs (vec int int less) int)
  (lambda (v left right less?)
    (let ((mid (array-ref v right)))
      (letrec ((uploop (subr vecs (int) int)
                 (lambda (i)
                   (let ((i (+ i 1)))
                     (if (and (< i right) (less? (array-ref v i) mid))
                         (uploop i)
                         i))))
               (downloop (subr vecs (int) int)
                 (lambda (j)
                   (let ((j (- j 1)))
                     (if (and (> j left) (less? mid (array-ref v j)))
                         (downloop j)
                         j))))
               (ploop (subr vecs (int int) int)
                 (lambda (i j)
                   (let* ((i (uploop i))
                          (j (downloop j)))
                     (let ((tmp (array-ref v i)))
                       (begin
                         (array-set! v i (array-ref v j))
                         (array-set! v j tmp)
                         (if (< i j)
                             (ploop i j)
                             (begin (array-set! v j (array-ref v i))
                                    (array-set! v i (array-ref v right))
                                    (array-set! v right tmp)
                                    i))))))))
        (ploop (- left 1) right)))))

(define* quick-1 (subr vecs (vec less) vec)
  (lambda (v less?)
    (letrec ((helper (subr (maxeff vecs (read (globals partition))) (int int) vec)
               (lambda (left right)
                 (if (< left right)
                     (let ((median (partition v left right less?)))
                       (if (< (- median left) (- right median))
                           (begin (helper left (- median 1))
                                  (helper (+ median 1) right))
                           (begin (helper (+ median 1) right)
                                  (helper left (- median 1)))))
                     v))))
      (helper 0 (- (array-length v) 1)))))

;;; A uniform [0,1] random number generator; is
;;; Pierre L'Ecuyer's generator from his paper
;;; "Good parameters and implementations for combined multiple
;;; recursive random number generators"
;;; available at his web site http://www.iro.umontreal.ca/~lecuyer
;;;
;;; Here in integers (see above): `random-flonum` returns x, its flonum
;;; being x/(m1 + 1).

(define m1 int 4294967087)
(define m2 int 4294944443)
(define a12 int 1403580)
(define a13n int 810728)
(define a21 int 527612)
(define a23n int 1370589)
(define seed vec
  (let ((seed (the vec (make-array 6 0))))  ; will be mutated
    (begin (array-set! seed 0 1) (array-set! seed 3 1) seed)))

(define* random-flonum (subr vecs () int)
  (lambda ()
    (let ((seed seed))  ; make it local
      (let ((p1 (- (* a12 (array-ref seed 1))
                   (* a13n (array-ref seed 0))))
            (p2 (- (* a21 (array-ref seed 5))
                   (* a23n (array-ref seed 3)))))
        (let ((k1 (quotient p1 m1))
              (k2 (quotient p2 m2))
              (ignore1 (array-set! seed 0 (array-ref seed 1)))
              (ignore3 (array-set! seed 3 (array-ref seed 4))))
          (let ((p1 (- p1 (* k1 m1)))
                (p2 (- p2 (* k2 m2)))
                (ignore2 (array-set! seed 1 (array-ref seed 2)))
                (ignore4 (array-set! seed 4 (array-ref seed 5))))
            (let ((p1 (if (< p1 0) (+ p1 m1) p1))
                  (p2 (if (< p2 0) (+ p2 m2) p2)))
              (begin
                (array-set! seed 2 p1)
                (array-set! seed 5 p2)
                (if (<= p1 p2)
                    (+ (- p1 p2) m1)
                    (- p1 p2))))))))))

(define* random (subr vecs (int) int)
  (lambda (n) (quotient (* n (random-flonum)) (+ m1 1))))

;;; Even with the improved random number generator,
;;; this benchmark still spends almost all of its time
;;; generating the random vector.  To make this a true
;;; quicksort benchmark, we generate a relatively small
;;; random vector and then sort many copies of it.

(define* vector-copy (subr vecs (vec) vec)
  (lambda (v)
    (let ((w (the vec (make-array (array-length v) 0))))
      (letrec ((loop (subr vecs (int) vec)
                 (lambda (i) (if (= i (array-length v)) w (begin (array-set! w i (array-ref v i)) (loop (+ i 1)))))))
        (loop 0)))))

;; Larceny's check: is v in order?
(define* sorted? (subr vecs (vec) bool)
  (lambda (v)
    (letrec ((loop (subr vecs (int) bool)
               (lambda (i)
                 (cond ((= i (array-length v)) #t)
                       ((not (<= (array-ref v (- i 1)) (array-ref v i))) #f)
                       (else (loop (+ i 1)))))))
      (loop 1))))

;; The inputs, where no compiler can fold them (Larceny's `hide`): globals,
;; which a later definition may replace.
(define input1 int 10000)
(define input2 int 1000000)
(define less? less (lambda (x y) (< x y)))
(define iterations int 2500)

(define v vec
  (let ((v (the vec (make-array input1 0))))
    (letrec ((fill (subr (maxeff vecs (read (globals random random-flonum seed m1 m2 a12 a13n a21 a23n input1 input2))) (int) vec)
               (lambda (i) (if (= i input1) v (begin (array-set! v i (random input2)) (fill (+ i 1)))))))
      (fill 0))))

(define* run (subr vecs (int vec) vec)
  (lambda (i result) (if (= i 0) result (run (- i 1) (quick-1 (vector-copy v) less?)))))
(sorted? (run iterations v))
