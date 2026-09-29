;;; TRIANGL -- Board game benchmark.
;;;
;;; From Larceny's R7RS benchmarks (test/Benchmarking/R7RS/src/triangl.scm),
;;; ported to FX-26. Larceny's input: 50 iterations of (test 22 1).
;;; Answer: (22 34 31 15 7 1 20 17 25 6 5 13 32).
;;;
;;; Vectors are arrays, and the global `*answer*`, which the benchmark
;;; assigns, a reference. FX-26 quotes only symbols, so each
;;; `(list->vector '(...))` is `list->array` of a list made with `list`;
;;; `list->array` and `array->list` (for `vector->list`) are written here.
;;; The `do` loop in `attempt` is a local `letrec` loop.

(define-type ints (listof int @heap))
(define-type ivec (arrayof int @heap))

(define* list-length (subr spin ((listof int acyclic)) int)
  (lambda (l) (if (null? l) 0 (+ 1 (list-length (cdr l))))))

(define* list->array
  (subr (maxeff (read @heap) (write @heap) (alloc @heap) spin) ((listof int acyclic)) ivec)
  (lambda (l)
    (let ((v (the ivec (make-array (list-length l) 0))))
      (letrec ((fill (subr (maxeff (read @heap) (write @heap) spin) (int (listof int acyclic)) ivec)
                 (lambda (i l)
                   (if (null? l)
                       v
                       (begin (array-set! v i (car l))
                              (fill (+ i 1) (cdr l)))))))
        (fill 0 l)))))

(define* array->list (subr (maxeff (read @heap) (alloc @heap) spin) (ivec) ints)
  (lambda (v)
    (letrec ((build (subr (maxeff (read @heap) (alloc @heap) spin) (int ints) ints)
               (lambda (i l)
                 (if (< i 0)
                     l
                     (build (- i 1) (cons (array-ref v i) l))))))
      (build (- (array-length v) 1) nil))))

(define *board* ivec
  (list->array
    (list 1 1 1 1 1 0 1 1 1 1 1 1 1 1 1 1)))
(define *sequence* ivec
  (list->array
    (list 0 0 0 0 0 0 0 0 0 0 0 0 0 0)))
(define *a* ivec
  (list->array
    (list 1 2 4 3 5 6 1 3 6 2 5 4 11 12 13 7 8 4 4 7 11 8 12 13 6 10 15 9 14 13 13 14 15 9 10 6 6)))
(define *b* ivec
  (list->array
    (list 2 4 7 5 8 9 3 6 10 5 9 8 12 13 14 8 9 5 2 4 7 5 8 9 3 6 10 5 9 8 12 13 14 8 9 5 5)))
(define *c* ivec
  (list->array
    (list 4 7 11 8 12 13 6 10 15 9 14 13 13 14 15 9 10 6 1 2 4 3 5 6 1 3 6 2 5 4 11 12 13 7 8 4 4)))

(define *answer* (ref (listof ints @heap) @heap) (new nil))

(define* attempt (subr (maxeff (read @heap) (write @heap) (alloc @heap) spin) (int int) bool)
  (lambda (i depth)
    (cond ((= depth 14)
           (begin
             (set *answer*
                  (cons (cdr (array->list *sequence*)) (get *answer*)))
             #t))
          ((and (= 1 (array-ref *board* (array-ref *a* i)))
                (= 1 (array-ref *board* (array-ref *b* i)))
                (= 0 (array-ref *board* (array-ref *c* i))))
           (begin
             (array-set! *board* (array-ref *a* i) 0)
             (array-set! *board* (array-ref *b* i) 0)
             (array-set! *board* (array-ref *c* i) 1)
             (array-set! *sequence* depth i)
             (letrec ((loop (subr (maxeff (read @heap) (write @heap) (alloc @heap) spin
                                          (read (globals *board* *sequence* *a* *b* *c* *answer* array->list attempt)))
                                  (int int) bool)
                        (lambda (j depth)
                          (if (or (= j 36) (attempt j depth))
                              #f
                              (loop (+ j 1) depth)))))
               (loop 0 (+ depth 1)))
             (array-set! *board* (array-ref *a* i) 1)
             (array-set! *board* (array-ref *b* i) 1)
             (array-set! *board* (array-ref *c* i) 0)
             #f))
          (else #f))))

(define* test (subr (maxeff (read @heap) (write @heap) (alloc @heap) spin) (int int) ints)
  (lambda (i depth)
    (begin
      (set *answer* nil)
      (attempt i depth)
      (car (get *answer*)))))

;; The inputs, where no compiler can fold them (Larceny's `hide`): globals,
;; which a later definition may replace.
(define input1 int 22)
(define input2 int 1)
(define iterations int 50)

(define* run (subr (maxeff (read @heap) (write @heap) (alloc @heap) spin) (int ints) ints)
  (lambda (i result) (if (= i 0) result (run (- i 1) (test input1 input2)))))
(run iterations nil)
