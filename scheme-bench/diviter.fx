;;; DIVITER -- Benchmark which divides by 2 using lists of n ()'s.
;;;
;;; From Larceny's R7RS benchmarks (test/Benchmarking/R7RS/src/diviter.scm),
;;; ported to FX-26. Larceny's input: 1000000 iterations of
;;; (iterative-div2 ll), ll a list of 1000 ()'s. Answer: 500, the length of
;;; the result, as Larceny checks it.
;;;
;;; The `do` loops are local `letrec` loops. `length` wants a list the
;;; checker knows is finite, so the answer is taken by `list-length`.

(define-type nils (listof (listof int @heap) @heap))

(define* create-n (subr (maxeff (alloc @heap) spin) (int) nils)
  (lambda (n)
    (letrec ((loop (subr (maxeff (alloc @heap) spin) (int nils) nils)
               (lambda (n a) (if (= n 0) a (loop (- n 1) (cons nil a))))))
      (loop n nil))))

(define* iterative-div2 (subr (maxeff (read @heap) (alloc @heap) spin) (nils) nils)
  (lambda (l)
    (letrec ((loop (subr (maxeff (read @heap) (alloc @heap) spin) (nils nils) nils)
               (lambda (l a) (if (null? l) a (loop (cdr (cdr l)) (cons (car l) a))))))
      (loop l nil))))

(define* list-length (subr (maxeff (read @heap) spin) (nils) int)
  (lambda (l) (if (null? l) 0 (+ 1 (list-length (cdr l))))))

;; The inputs, where no compiler can fold them (Larceny's `hide`): globals,
;; which a later definition may replace.
(define input1 int 1000)
(define iterations int 1000000)
(define ll nils (create-n input1))

(define* run (subr (maxeff (read @heap) (alloc @heap) spin) (int nils) nils)
  (lambda (i result) (if (= i 0) result (run (- i 1) (iterative-div2 ll)))))
(list-length (run iterations nil))
