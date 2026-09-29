;;; LIST -- List benchmark for (scheme list).
;;;
;;; From Larceny's R7RS benchmarks (test/Benchmarking/R7RS/src/list.scm),
;;; ported to FX-26. Larceny's input: 10 iterations of (go 8).
;;; Answer: ((x0 x1 x2 x3 x4 x5 x6 x7)).
;;;
;;; FX-26 has no (scheme list), so the SRFI 1 procedures the benchmark
;;; calls are written here, after Larceny's own (the reference
;;; implementation, lib/SRFI/srfi/%3a1.sls), each for the one element type
;;; it is used at, and the one-list `fold`, `any` and `reduce` inlined into
;;; the procedures that call them as loops.
;;; - FX-26 has no `eq?` on pairs. `lset-union eq?` compares subsets
;;;   (lists) with `eq?`; here with `syms=?`, element by element, which
;;;   gives the same answers (no two distinct subsets in the benchmark are
;;;   equal) and stops at the first symbol, since the subsets compared
;;;   always differ there or in length. Its `(eq? lis ans)` shortcut, never
;;;   taken here, is left out.
;;; - `filter`'s `eq?` test that shares an unfiltered tail is left out too:
;;;   the kept tail is consed afresh (one permutation is kept, of 40320).

(define-type syms (listof symbol @heap))
(define-type sets (listof syms @heap))
(define-type ints (listof int @heap))
(define-type strs (listof string @heap))
(define-effect lists (maxeff (read @heap) (alloc @heap) spin))

;; SRFI 1's iota, from 0: counts down from the last value.
(define* iota (subr lists (int) ints)
  (lambda (count)
    (letrec ((loop (subr lists (int int ints) ints)
               (lambda (count val ans)
                 (if (<= count 0) ans (loop (- count 1) (- val 1) (cons val ans))))))
      (loop count (- count 1) nil))))

(define* take (subr lists (syms int) syms)
  (lambda (lis k) (if (= k 0) nil (cons (car lis) (take (cdr lis) (- k 1))))))

(define* drop (subr lists (syms int) syms)
  (lambda (lis k) (if (= k 0) lis (drop (cdr lis) (- k 1)))))

(define* append2 (subr lists (syms syms) syms)
  (lambda (xs ys) (if (null? xs) ys (cons (car xs) (append2 (cdr xs) ys)))))

(define* append-sets (subr lists (sets sets) sets)
  (lambda (xs ys) (if (null? xs) ys (cons (car xs) (append-sets (cdr xs) ys)))))

(define* syms-length (subr lists (syms) int)
  (lambda (xs) (if (null? xs) 0 (+ 1 (syms-length (cdr xs))))))

;; equal? on lists of symbols.
(define* syms=? (subr lists (syms syms) bool)
  (lambda (a b)
    (cond ((null? a) (null? b))
          ((null? b) #f)
          ((symbol=? (car a) (car b)) (syms=? (cdr a) (cdr b)))
          (else #f))))

;; (member x lis eq?), for a symbol: #t where SRFI 1 returns the tail.
(define* memq? (subr lists (symbol syms) bool)
  (lambda (x lis)
    (cond ((null? lis) #f) ((symbol=? x (car lis)) #t) (else (memq? x (cdr lis))))))

;; (member perm subsets), equal? on lists of symbols.
(define* member-syms? (subr lists (syms sets) bool)
  (lambda (x lis)
    (cond ((null? lis) #f) ((syms=? x (car lis)) #t) (else (member-syms? x (cdr lis))))))

;; (lset-adjoin eq? lis elt), one element.
(define* lset-adjoin (subr lists (syms symbol) syms)
  (lambda (lis elt) (if (memq? elt lis) lis (cons elt lis))))

;; (any (lambda (x) (= x elt)) ans), `=` being the list comparison above.
(define* any-same? (subr lists (sets syms) bool)
  (lambda (ans elt)
    (cond ((null? ans) #f) ((syms=? (car ans) elt) #t) (else (any-same? (cdr ans) elt)))))

;; (lset-union eq? a b): reduce over (a b) is ans = a, lis = b, and each
;; element of lis not yet in ans is consed onto it, by fold.
(define* lset-union (subr lists (sets sets) sets)
  (lambda (ans0 lis0)
    (letrec ((fold (subr (maxeff lists (read (globals any-same? syms=?))) (sets sets) sets)
               (lambda (lis ans)
                 (if (null? lis)
                     ans
                     (fold (cdr lis)
                           (if (any-same? ans (car lis)) ans (cons (car lis) ans)))))))
      (cond ((null? lis0) ans0)
            ((null? ans0) lis0)
            (else (fold lis0 ans0))))))

;; (concatenate lists) = (reduce-right append '() lists).
(define* concatenate (subr lists ((listof sets @heap)) sets)
  (lambda (lis)
    (letrec ((recur (subr (maxeff lists (read (globals append-sets))) (sets (listof sets @heap)) sets)
               (lambda (head lis)
                 (if (null? lis) head (append-sets head (recur (car lis) (cdr lis)))))))
      (if (null? lis) (the sets nil) (recur (car lis) (cdr lis))))))

(define* symbols (subr lists (int) syms)
  (lambda (n)
    (letrec ((map-number->string (subr lists (ints) strs)
               (lambda (xs) (if (null? xs) nil (cons (int->string (car xs)) (map-number->string (cdr xs))))))
             (map-prefix (subr lists (strs) strs)
               (lambda (xs) (if (null? xs) nil (cons (string-append "x" (car xs)) (map-prefix (cdr xs))))))
             (map-string->symbol (subr lists (strs) syms)
               (lambda (xs) (if (null? xs) nil (cons (string->symbol (car xs)) (map-string->symbol (cdr xs)))))))
      (map-string->symbol (map-prefix (map-number->string (iota n)))))))

(define* powerset (subr lists (syms) sets)
  (lambda (universe)
    (if (null? universe)
        (cons (the syms nil) nil)
        (let* ((x (car universe))
               (u2 (cdr universe))
               (pu2 (powerset u2)))
          (letrec ((map-adjoin (subr (maxeff lists (read (globals lset-adjoin memq?))) (sets) sets)
                     (lambda (ys) (if (null? ys) nil (cons (lset-adjoin (car ys) x) (map-adjoin (cdr ys)))))))
            (lset-union pu2 (map-adjoin pu2)))))))

(define* permutations (subr lists (syms) sets)
  (lambda (universe)
    (if (null? universe)
        (cons (the syms nil) nil)
        (let* ((x (car universe))
               (u2 (cdr universe))
               (perms2 (permutations u2)))
          (letrec ((map-i (subr (maxeff lists (read (globals append2 take drop))) (syms ints) sets)
                     (lambda (perm is)
                       (if (null? is)
                           nil
                           (cons (append2 (take perm (car is)) (cons x (drop perm (car is))))
                                 (map-i perm (cdr is))))))
                   (map-perm (subr (maxeff lists (read (globals append2 take drop iota syms-length))) (sets) (listof sets @heap))
                     (lambda (perms)
                       (if (null? perms)
                           nil
                           (cons (map-i (car perms) (iota (+ 1 (syms-length (car perms)))))
                                 (map-perm (cdr perms)))))))
            (concatenate (map-perm perms2)))))))

(define* go (subr lists (int) sets)
  (lambda (n)
    (let* ((universe (symbols n))
           (subsets (powerset universe))
           (perms (permutations universe)))
      (letrec ((filter (subr (maxeff lists (read (globals member-syms? syms=?))) (sets) sets)
                 (lambda (lis)
                   (cond ((null? lis) nil)
                         ((member-syms? (car lis) subsets) (cons (car lis) (filter (cdr lis))))
                         (else (filter (cdr lis)))))))
        (filter perms)))))

;; The inputs, where no compiler can fold them (Larceny's `hide`): globals,
;; which a later definition may replace.
(define input1 int 8)
(define iterations int 10)

(define* run (subr lists (int sets) sets)
  (lambda (i result) (if (= i 0) result (run (- i 1) (go input1)))))
(run iterations nil)
