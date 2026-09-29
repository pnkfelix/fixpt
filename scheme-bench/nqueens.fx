;;; NQUEENS -- Compute number of solutions to 8-queens problem.
;;;
;;; From Larceny's R7RS benchmarks (test/Benchmarking/R7RS/src/nqueens.scm),
;;; ported to FX-26. Larceny's input: 10 iterations of (nqueens 13).
;;; Answer: 73712.

(define-type ints (listof int @heap))

(define* append2 (subr (maxeff (read @heap) (alloc @heap) spin) (ints ints) ints)
  (lambda (xs ys) (if (null? xs) ys (cons (car xs) (append2 (cdr xs) ys)))))

(define* nqueens (subr (maxeff (read @heap) (alloc @heap) spin) (int) int)
  (lambda (n)
    (letrec ((iota1 (subr (maxeff (alloc @heap) spin) (int ints) ints)
               (lambda (i l) (if (= i 0) l (iota1 (- i 1) (cons i l)))))
             (ok? (subr (maxeff (read @heap) spin) (int int ints) bool)
               (lambda (row dist placed)
                 (if (null? placed)
                     #t
                     (and (not (= (car placed) (+ row dist)))
                          (not (= (car placed) (- row dist)))
                          (ok? row (+ dist 1) (cdr placed))))))
             (my-try (subr (maxeff (read @heap) (alloc @heap) spin (read (globals append2))) (ints ints ints) int)
               (lambda (x y z)
                 (if (null? x)
                     (if (null? y) 1 0)
                     (+ (if (ok? (car x) 1 z)
                            (my-try (append2 (cdr x) y) nil (cons (car x) z))
                            0)
                        (my-try (cdr x) (cons (car x) y) z))))))
      (my-try (iota1 n nil) nil nil))))

(define input int 13)
(define iterations int 10)

(define* run (subr (maxeff (read @heap) (alloc @heap) spin) (int int) int)
  (lambda (i result) (if (= i 0) result (run (- i 1) (nqueens input)))))
(run iterations 0)
