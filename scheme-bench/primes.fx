;;; PRIMES -- Compute primes less than n, written by Eric Mohr.
;;;
;;; From Larceny's R7RS benchmarks (test/Benchmarking/R7RS/src/primes.scm),
;;; ported to FX-26. Larceny's input: 10000 iterations of (primes<= 1000).
;;; Answer: the 168 primes up to 1000, (2 3 5 7 ... 983 991 997).
;;;
;;; `remainder` is `modulo`, the same on these positive numbers. The body
;;; of `sieve`'s `letrec` says its type with `the`: a `letrec`'s body is not
;;; checked against the type expected of it, as a `let`'s is.

(define-type ints (listof int @heap))

(define* interval-list (subr (maxeff (alloc @heap) spin) (int int) ints)
  (lambda (m n)
    (if (> m n)
        nil
        (cons m (interval-list (+ 1 m) n)))))

(define* sieve (subr (maxeff (read @heap) (alloc @heap) spin) (ints) ints)
  (lambda (l)
    (letrec ((remove-multiples (subr (maxeff (read @heap) (alloc @heap) spin) (int ints) ints)
               (lambda (n l)
                 (if (null? l)
                     nil
                     (if (= (modulo (car l) n) 0)
                         (remove-multiples n (cdr l))
                         (cons (car l)
                               (remove-multiples n (cdr l))))))))
      (the ints
        (if (null? l)
            nil
            (cons (car l)
                  (sieve (remove-multiples (car l) (cdr l)))))))))

(define* primes<= (subr (maxeff (read @heap) (alloc @heap) spin) (int) ints)
  (lambda (n)
    (sieve (interval-list 2 n))))

;; The inputs, where no compiler can fold them (Larceny's `hide`): globals,
;; which a later definition may replace.
(define input1 int 1000)
(define iterations int 10000)

(define* run (subr (maxeff (read @heap) (alloc @heap) spin) (int ints) ints)
  (lambda (i result) (if (= i 0) result (run (- i 1) (primes<= input1)))))
(run iterations nil)
