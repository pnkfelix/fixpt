;;; MPERM -- memory system benchmark using Zaks's permutation generator
;;;
;;; File:         perm9.sch
;;; Description:  memory system benchmark using Zaks's permutation generator
;;; Author:       Lars Hansen, Will Clinger, and Gene Luks
;;; Created:      18-Mar-94
;;; Language:     Scheme
;;; Status:       Public Domain
;;;
;;; From Larceny's R7RS benchmarks (test/Benchmarking/R7RS/src/mperm.scm),
;;; ported to FX-26. Larceny's input: (MpermNKL-benchmark 20 10 2 1), which
;;; runs its thunk 20 times.
;;; Answer: 199584000, the sum of the permuted integers over all
;;; permutations in the queue's oldest list, (/ (* N (+ N 1) (factorial
;;; N)) 2), computed as Larceny's check computes it (`sumlists`), once,
;;; after the iterations. (mperm.input's "result", 16329600, is that sum
;;; for N=9, left from the old parameters; the input says it is ignored,
;;; and Larceny's check computes it from N.)
;;;
;;; The `set!`s of `permutations`' local `x` and `perms` are refs, the
;;; queue an array, `do` a named loop. The argument checks, the id string
;;; and `run-benchmark` are left out; Larceny's check of the result (the
;;; first permutation of the oldest and newest lists `equal?`, which with
;;; K=2 and L=1 are the same list) is only its sum.

; This benchmark is in three parts.  Each tests a different aspect of
; the memory system.
;
;    storage allocation (while generating no garbage)
;    storage allocation and garbage collection at equilibrium
;    traversal of a large, linked, self-sharing structure
;
; The perm9 benchmark generates a list of all 362880 permutations of
; the first 9 integers, allocating 1349288 pairs (typically 10,794,304
; bytes), all of which goes into the generated list.  (That is, the
; perm9 benchmark generates absolutely no garbage.)  This represents
; a savings of about 63% over the storage that would be required by
; an unshared list of permutations.  The generated permutations are
; in order of a grey code that bears no obvious relationship to a
; lexicographic order.
;
; The tenperm9 benchmark repeats the perm9 benchmark 10 times, so it
; allocates and reclaims 13492880 pairs (typically 107,943,040 bytes).
; The live storage peaks at twice the storage that is allocated by the
; perm9 benchmark.  At the end of each iteration, the oldest half of
; the live storage becomes garbage.  Object lifetimes are distributed
; uniformly between 10.3 and 20.6 megabytes.
;
; The tenperm9 benchmark is the perm10:9:2:1 special case of the
; MpermNKL benchmark, which allocates a queue of size K and then
; performs M iterations of the following operation:  Fill the queue
; with individually computed copies of all permutations of a list of
; size N, and then remove the oldest L copies from the queue.  At the
; end of each iteration, the oldest L/K of the live storage becomes
; garbage, and object lifetimes are distributed uniformly between two
; volumes that depend upon N, K, and L.
;
; As a check on the result, and to preclude overly sophisticated
; compiler optimizations,  we compute the sum of the permuted
; integers over all permutations.

; Date: Thu, 17 Mar 94 19:43:32 -0800
; From: luks@sisters.cs.uoregon.edu
; To: will
; Subject: Pancake flips
;
; Procedure P_n generates a grey code of all perms of n elements
; on top of stack ending with reversal of starting sequence
;
; F_n is flip of top n elements.
;
;
; procedure P_n
;
;   if n>1 then
;     begin
;        repeat   P_{n-1},F_n   n-1 times;
;        P_{n-1}
;     end
;

(define-type ints (listof int @heap))
(define-type perms (listof ints @heap))
(define-effect lists (maxeff (read @heap) (write @heap) (alloc @heap) spin))

(define* list-length (subr lists (ints) int)
  (lambda (xs)
    (letrec ((loop (subr lists (ints int) int)
               (lambda (xs n) (if (null? xs) n (loop (cdr xs) (+ n 1))))))
      (loop xs 0))))

(define* permutations (subr lists (ints) perms)
  (lambda (x0)
    (let ((x (the (ref ints @heap) (new x0)))
          (perms (the (ref perms @heap) (new (cons x0 nil)))))
      (letrec ((P (subr lists (int) unit)
                 (lambda (n)
                   (if (> n 1)
                       (letrec ((do-j (subr lists (int) unit)
                                  (lambda (j)
                                    (if (= j 0)
                                        (P (- n 1))
                                        (begin (P (- n 1))
                                               (F n)
                                               (do-j (- j 1)))))))
                         (do-j (- n 1)))
                       #u)))
               (F (subr lists (int) unit)
                 (lambda (n)
                   (begin (set x (revloop (get x) n (list-tail (get x) n)))
                          (set perms (cons (get x) (get perms))))))
               (revloop (subr lists (ints int ints) ints)
                 (lambda (x n y)
                   (if (= n 0)
                       y
                       (revloop (cdr x)
                                (- n 1)
                                (cons (car x) y)))))
               (list-tail (subr lists (ints int) ints)
                 (lambda (x n)
                   (if (= n 0)
                       x
                       (list-tail (cdr x) (- n 1))))))
        (begin (P (list-length (get x)))
               (get perms))))))

; Given a list of lists of numbers, returns the sum of the sums
; of those lists.
;
; for (; x != NULL; x = x->rest)
;     for (y = x->first; y != NULL; y = y->rest)
;         sum = sum + y->first;

(define* sumlists (subr lists (perms) int)
  (lambda (x)
    (letrec ((outer (subr lists (perms int) int)
               (lambda (x sum)
                 (if (null? x)
                     sum
                     (outer (cdr x) (inner (car x) sum)))))
             (inner (subr lists (ints int) int)
               (lambda (y sum)
                 (if (null? y) sum (inner (cdr y) (+ sum (car y)))))))
      (outer x 0))))

(define* one..n (subr lists (int) ints)
  (lambda (n)
    (letrec ((loop (subr lists (int ints) ints)
               (lambda (n p) (if (= n 0) p (loop (- n 1) (cons n p))))))
      (loop n nil))))

;; The inputs, where no compiler can fold them (Larceny's `hide`): globals,
;; which a later definition may replace.
(define m int 20)
(define n int 10)
(define k int 2)
(define ell int 1)

(define queue (arrayof perms @heap) (make-array k nil))

; Fills queue positions [i, j).
(define* fill-queue (subr lists (int int) unit)
  (lambda (i j)
    (if (< i j)
        (begin (array-set! queue i (permutations (one..n n)))
               (fill-queue (+ i 1) j))
        #u)))

; Removes ell elements from queue.
(define* flush-queue (subr lists () unit)
  (lambda ()
    (letrec ((loop (subr (maxeff lists (read (globals queue k ell))) (int) unit)
               (lambda (i)
                 (if (< i k)
                     (begin (array-set! queue
                                        i
                                        (let ((j (+ i ell)))
                                          (if (< j k)
                                              (array-ref queue j)
                                              nil)))
                            (loop (+ i 1)))
                     #u))))
      (loop 0))))

(fill-queue 0 (- k ell))

(define* run (subr lists (int) (arrayof perms @heap))
  (lambda (i)
    (begin (fill-queue (- k ell) k)
           (flush-queue)
           (if (= i 1) queue (run (- i 1))))))
(sumlists (array-ref (run m) 0))
