;;; NTAKL -- The TAKeuchi function using lists as counters,
;;; with an alternative boolean expression.
;;;
;;; From Larceny's R7RS benchmarks (test/Benchmarking/R7RS/src/ntakl.scm),
;;; ported to FX-26. Larceny's input: 1 iteration of (mas l40 l20 l12),
;;; lN the list (N N-1 ... 1). Answer: 13, the length of the result, as
;;; Larceny checks it.
;;;
;;; Larceny reads its three lists; here they are made by the benchmark's own
;;; `listn`, from their lengths. `l18`, `l12` and `l6`, which the original
;;; defines and never uses, are left out. `length` wants a list the checker
;;; knows is finite, so the answer is taken by `list-length`.

(define-type ints (listof int @heap))

(define* listn (subr (maxeff (alloc @heap) spin) (int) ints)
  (lambda (n)
    (if (= n 0)
        nil
        (cons n (listn (- n 1))))))

; Part of the fun of this benchmark is seeing how well the compiler
; can understand this ridiculous code, which dates back to the original
; Common Lisp.  So it probably isn't a good idea to improve upon it.

(define* shorterp (subr (maxeff (read @heap) spin) (ints ints) bool)
  (lambda (x y)
    (cond ((null? y) #f)
          ((null? x) #t)
          (else
           (shorterp (cdr x) (cdr y))))))

(define* mas (subr (maxeff (read @heap) spin) (ints ints ints) ints)
  (lambda (x y z)
    (if (not (shorterp y x))
        z
        (mas (mas (cdr x) y z)
             (mas (cdr y) z x)
             (mas (cdr z) x y)))))

(define* list-length (subr (maxeff (read @heap) spin) (ints) int)
  (lambda (l) (if (null? l) 0 (+ 1 (list-length (cdr l))))))

;; The inputs, where no compiler can fold them (Larceny's `hide`): globals,
;; which a later definition may replace.
(define length1 int 40)
(define length2 int 20)
(define length3 int 12)
(define input1 ints (listn length1))
(define input2 ints (listn length2))
(define input3 ints (listn length3))
(define iterations int 1)

(define* run (subr (maxeff (read @heap) spin) (int ints) ints)
  (lambda (i result) (if (= i 0) result (run (- i 1) (mas input1 input2 input3)))))
(list-length (run iterations nil))
