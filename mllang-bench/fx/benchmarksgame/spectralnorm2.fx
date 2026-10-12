;;; SPECTRALNORM -- the spectral norm of an infinite matrix, by the power
;;; method.
;;;
;;; From the Computer Language Benchmarks Game, via Sandmark
;;; (benchmarksgame/spectralnorm2.ml: Sebastien Loisel, Troestler
;;; Christophe, Mauricio Fernandez), ported to FX-26. Size: n = 2000, the
;;; original's default. Answer: the norm, as `f64->string` writes it (the original
;;; prints it to 9 places).
;;;
;;; OCaml's float arrays, raw, are flat arrays of `f64`s here. Each row's
;;; sum, a `ref` in the original, is carried round its loop.

(define-type vec (flatarrayof f64 @heap))

(define* eval-a (subr pure (int int) f64)
  (lambda (i j) (f64/ 1. (int->f64 (+ (+ (quotient (* (+ i j) (+ (+ i j) 1)) 2) i) 1)))))

;; Row `i`'s sum of A(i, j) u(j) (or, `t`, of A(j, i) u(j)), from `j`.
(define* row (subr (maxeff (read @heap) spin (read (globals eval-a))) (bool vec int int int f64) f64)
  (lambda (t u n i j sum)
    (if (= j n)
        sum
        (row t u n i (+ j 1)
             (f64+ sum (f64* (if t (eval-a j i) (eval-a i j)) (flatarray-ref u j)))))))

(define* times (subr (maxeff (read @heap) (write @heap) spin (read (globals row eval-a))) (bool vec vec int) unit)
  (lambda (t u v i)
    (let ((n (flatarray-length v)))
      (if (= i n)
          #u
          (begin (flatarray-set! v i (row t u n i 0 0.)) (times t u v (+ i 1)))))))

(define* ata-times (subr (maxeff (alloc @heap) (read @heap) (write @heap) spin (read (globals times row eval-a))) (vec vec) unit)
  (lambda (u v)
    (let ((w (the vec (make-flatarray (f64-flat) (flatarray-length u) 0.))))
      (begin (times #f u w 0) (times #t w v 0)))))

(define* sums (subr (maxeff (read @heap) spin) (vec vec int f64 f64) f64)
  (lambda (u v i vv vbv)
    (if (= i (flatarray-length v))
        (f64-sqrt (f64/ vbv vv))
        (let ((vi (flatarray-ref v i)))
          (sums u v (+ i 1) (f64+ vv (f64* vi vi)) (f64+ vbv (f64* (flatarray-ref u i) vi)))))))

(define* doit
  (subr (maxeff (alloc @heap) (read @heap) (write @heap) spin (read (globals ata-times times row eval-a sums)))
        (int) string)
  (lambda (n)
    (let ((u (the vec (make-flatarray (f64-flat) n 1.)))
          (v (the vec (make-flatarray (f64-flat) n 0.))))
      (letrec ((ten (subr (maxeff (alloc @heap) (read @heap) (write @heap) spin
                                  (read (globals ata-times times row eval-a)))
                          (int) unit)
                 (lambda (k) (if (= k 10) #u (begin (ata-times u v) (ata-times v u) (ten (+ k 1)))))))
        (begin (ten 0) (f64->string (sums u v 0 0. 0.)))))))

(doit 2000)
