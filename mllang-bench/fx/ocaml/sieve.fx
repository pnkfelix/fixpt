;;; SIEVE -- Eratosthenes' sieve, on lists, with a higher-order filter.
;;;
;;; From OCaml's classic test programs (testsuite/tests/misc/sieve.ml, ocaml
;;; commit 7da997d28b1a), ported to FX-26. The original prints the primes
;;; up to 50000, once, with `do_list`; the port runs (sieve 50000)
;;; `iterations` = 100 times, and its `do_list` adds each prime into a ref
;;; where the original prints it. Answer: 121013308, the sum of the 5133
;;; numbers the reference output lists (the primes below 50000).

(define-type ints (listof int @heap))

;; interval min max = [min; min+1; ...; max-1; max]
(define* interval (subr (maxeff (alloc @heap) spin) (int int) ints)
  (lambda (min max)
    (if (> min max) nil (cons min (interval (+ min 1) max)))))

;; filter p L returns the list of the elements in list L
;; that satisfy predicate p
(define* filter (subr (maxeff (read @heap) (alloc @heap) spin) ((subr pure (int) bool) ints) ints)
  (lambda (p l)
    (if (null? l)
        nil
        (let ((a (car l)) (r (cdr l)))
          (if (p a) (cons a (filter p r)) (filter p r))))))

;; Application: removing all numbers multiple of n from a list of integers
(define* remove-multiples-of (subr (maxeff (read @heap) (alloc @heap) spin) (int ints) ints)
  (lambda (n l)
    (filter (lambda ((m int)) (not (= (modulo m n) 0))) l)))

;; The sieve itself
(define* sieve (subr (maxeff (read @heap) (alloc @heap) spin) (int) ints)
  (lambda (max)
    (letrec ((filter-again (subr (maxeff (read @heap) (alloc @heap) spin (read (globals remove-multiples-of filter))) (ints) ints)
               (lambda (l)
                 (if (null? l)
                     nil
                     (let ((n (car l)) (r (cdr l)))
                       (if (> (* n n) max)
                           l
                           (cons n (filter-again (remove-multiples-of n r)))))))))
      (filter-again (interval 2 max)))))

(define* do-list (subr (maxeff (read @heap) (write @heap) spin) ((subr (maxeff (read @heap) (write @heap)) (int) unit) ints) unit)
  (lambda (f l)
    (if (null? l) #u (begin (f (car l)) (do-list f (cdr l))))))

;; The inputs, where no compiler can fold them: globals.
(define input int 50000)
(define iterations int 100)

(define* main (subr (maxeff (read @heap) (write @heap) (alloc @heap) spin) () int)
  (lambda ()
    (let ((total (the (ref int @heap) (new 0))))
      (begin
        (do-list (lambda ((n int)) (set total (+ (get total) n))) (sieve input))
        (get total)))))

(define* run (subr (maxeff (read @heap) (write @heap) (alloc @heap) spin) (int int) int)
  (lambda (i result) (if (= i 0) result (run (- i 1) (main)))))
(run iterations 0)
