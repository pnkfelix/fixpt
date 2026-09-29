;;; ARRAY1 -- One of the Kernighan and Van Wyk benchmarks.
;;;
;;; From Larceny's R7RS benchmarks (test/Benchmarking/R7RS/src/array1.scm),
;;; ported to FX-26. Larceny's input: 1 iteration of (go 500 1000000).
;;; Answer: 1000000.
;;;
;;; Vectors are arrays; `(make-vector n)`, whose elements are unspecified,
;;; is `(make-array n 0)`. The `do` loops and the named `let` are local
;;; `letrec` loops. `go`'s result starts as 0 where Larceny's starts as
;;; '(), which it returns only when asked for no repeats.

(define-type ivec (arrayof int @heap))

(define* create-x (subr (maxeff (alloc @heap) (write @heap) spin) (int) ivec)
  (lambda (n)
    (let ((result (the ivec (make-array n 0))))
      (letrec ((loop (subr (maxeff (write @heap) spin) (int) ivec)
                 (lambda (i)
                   (if (>= i n)
                       result
                       (begin (array-set! result i i)
                              (loop (+ i 1)))))))
        (loop 0)))))

(define* create-y (subr (maxeff (alloc @heap) (read @heap) (write @heap) spin) (ivec) ivec)
  (lambda (x)
    (let* ((n (array-length x))
           (result (the ivec (make-array n 0))))
      (letrec ((loop (subr (maxeff (read @heap) (write @heap) spin) (int) ivec)
                 (lambda (i)
                   (if (< i 0)
                       result
                       (begin (array-set! result i (array-ref x i))
                              (loop (- i 1)))))))
        (loop (- n 1))))))

(define* my-try (subr (maxeff (alloc @heap) (read @heap) (write @heap) spin) (int) int)
  (lambda (n)
    (array-length (create-y (create-x n)))))

(define* go (subr (maxeff (alloc @heap) (read @heap) (write @heap) spin) (int int) int)
  (lambda (m n)
    (letrec ((loop (subr (maxeff (alloc @heap) (read @heap) (write @heap) spin (read (globals create-x create-y my-try))) (int int) int)
               (lambda (repeat result)
                 (if (> repeat 0)
                     (loop (- repeat 1) (my-try n))
                     result))))
      (loop m 0))))

;; The inputs, where no compiler can fold them (Larceny's `hide`): globals,
;; which a later definition may replace.
(define count int 500)
(define input1 int 1000000)
(define iterations int 1)

(define* run (subr (maxeff (alloc @heap) (read @heap) (write @heap) spin) (int int) int)
  (lambda (i result) (if (= i 0) result (run (- i 1) (go count input1)))))
(run iterations 0)
