;;; QUICKSORT -- quicksort of an int array, with while loops and refs;
;;; "Good test for loops. Best compiled with -unsafe."
;;;
;;; From OCaml's classic test programs (testsuite/tests/misc-unsafe/
;;; quicksort.ml, ocaml commit 7da997d28b1a), ported to FX-26. The original
;;; sorts 50000 pseudo-random numbers with `qsort`, then 50000 more with
;;; `qsort2`, checks each result, and prints "OK" twice (the reference
;;; output). The port does that `iterations` = 30 times, the generator's
;;; seed running on, and its value is the number of checks passed. Answer:
;;; 60 (with `iterations` 1, 2: the reference's two "OK"s).
;;;
;;; What the port changes:
;;; - `while` loops are local recursive procedures; the loop variables stay
;;;   refs, as in the original.
;;; - The generator: OCaml computes `seed * 25173 + 17431` in 63 bits,
;;;   wrapping, and keeps the low 12 bits. FX-26's integers are checked for
;;;   overflow, so the port keeps the seed modulo 2^32, which leaves those
;;;   low bits, and so every number drawn, as they are.
;;; - `exception Failed`, raised from the checking loops and caught at the
;;;   end, is a prompt tag: `raise Failed` aborts to it.

(define-type arr (arrayof int @heap))
(define-effect heapy (maxeff (read @heap) (write @heap) (alloc @heap) spin))

(define* qsort (subr heapy (int int arr) unit)
  (lambda (lo hi a)
    (if (< lo hi)
        (let ((i (the (ref int @heap) (new lo)))
              (j (the (ref int @heap) (new hi)))
              (pivot (array-ref a hi)))
          (letrec ((up (subr heapy () unit)
                     (lambda ()
                       (if (and (< (get i) hi) (<= (array-ref a (get i)) pivot))
                           (begin (set i (+ (get i) 1)) (up))
                           #u)))
                   (down (subr heapy () unit)
                     (lambda ()
                       (if (and (> (get j) lo) (>= (array-ref a (get j)) pivot))
                           (begin (set j (- (get j) 1)) (down))
                           #u)))
                   (outer (subr heapy () unit)
                     (lambda ()
                       (if (< (get i) (get j))
                           (begin
                             (up)
                             (down)
                             (if (< (get i) (get j))
                                 (let ((temp (array-ref a (get i))))
                                   (begin (array-set! a (get i) (array-ref a (get j)))
                                          (array-set! a (get j) temp)))
                                 #u)
                             (outer))
                           #u))))
            (begin
              (outer)
              (let ((temp (array-ref a (get i))))
                (begin (array-set! a (get i) (array-ref a hi))
                       (array-set! a hi temp)))
              (qsort lo (- (get i) 1) a)
              (qsort (+ (get i) 1) hi a))))
        #u)))

;; Same but abstract over the comparison to force spilling

(define cmp (subr pure (int int) int) (lambda (i j) (- i j)))

(define* qsort2 (subr heapy (int int arr) unit)
  (lambda (lo hi a)
    (if (< lo hi)
        (let ((i (the (ref int @heap) (new lo)))
              (j (the (ref int @heap) (new hi)))
              (pivot (array-ref a hi)))
          (letrec ((up (subr (maxeff heapy (read (globals cmp))) () unit)
                     (lambda ()
                       (if (and (< (get i) hi) (<= (cmp (array-ref a (get i)) pivot) 0))
                           (begin (set i (+ (get i) 1)) (up))
                           #u)))
                   (down (subr (maxeff heapy (read (globals cmp))) () unit)
                     (lambda ()
                       (if (and (> (get j) lo) (>= (cmp (array-ref a (get j)) pivot) 0))
                           (begin (set j (- (get j) 1)) (down))
                           #u)))
                   (outer (subr (maxeff heapy (read (globals cmp))) () unit)
                     (lambda ()
                       (if (< (get i) (get j))
                           (begin
                             (up)
                             (down)
                             (if (< (get i) (get j))
                                 (let ((temp (array-ref a (get i))))
                                   (begin (array-set! a (get i) (array-ref a (get j)))
                                          (array-set! a (get j) temp)))
                                 #u)
                             (outer))
                           #u))))
            (begin
              (outer)
              (let ((temp (array-ref a (get i))))
                (begin (array-set! a (get i) (array-ref a hi))
                       (array-set! a hi temp)))
              (qsort2 lo (- (get i) 1) a)
              (qsort2 (+ (get i) 1) hi a))))
        #u)))

;; Test

(define seed (ref int @heap) (new 0))

(define* random (subr (maxeff (read @heap) (write @heap)) () int)
  (lambda ()
    (begin
      (set seed (modulo (+ (* (get seed) 25173) 17431) 4294967296))
      (modulo (get seed) 4096))))

;; exception Failed
(define failed (prompt-tag bool unit (maxeff heapy (read (globals failed))) @f)
  (make-continuation-prompt-tag))

(define* test-sort (subr (maxeff heapy (read @globals)) ((subr (maxeff heapy (read @globals)) (int int arr) unit) int) bool)
  (lambda (sort-fun size)
    (let ((a (the arr (make-array size 0)))
          (check (the arr (make-array 4096 0))))
      (letrec ((fill (subr (maxeff heapy (read (globals random seed))) (int) unit)
                 (lambda (i)
                   (if (<= i (- size 1))
                       (let ((n (random)))
                         (begin (array-set! a i n)
                                (array-set! check n (+ (array-ref check n) 1))
                                (fill (+ i 1))))
                       #u))))
        (begin
          (fill 0)
          (sort-fun 0 (- size 1) a)
          (prompt failed
            ;; The checking loops are bound inside the prompt, so that their
            ;; types, which mention @f, do not stop it delimiting.
            (letrec ((scan (subr (maxeff heapy (goto @f) (read (globals failed))) (int) unit)
                     (lambda (i)
                       (if (<= i (- size 1))
                           (begin
                             (if (> (array-ref a (- i 1)) (array-ref a i))
                                 (abort-current-continuation failed #u)
                                 #u)
                             (array-set! check (array-ref a i) (- (array-ref check (array-ref a i)) 1))
                             (scan (+ i 1)))
                           #u)))
                   (zero (subr (maxeff heapy (goto @f) (read (globals failed))) (int) unit)
                     (lambda (i)
                       (if (<= i 4095)
                           (begin
                             (if (not (= (array-ref check i) 0))
                                 (abort-current-continuation failed #u)
                                 #u)
                             (zero (+ i 1)))
                           #u))))
              (begin
                (array-set! check (array-ref a 0) (- (array-ref check (array-ref a 0)) 1))
                (scan 1)
                (zero 0)
                #t))
            (lambda (u) #f)))))))

;; The inputs, where no compiler can fold them: globals.
(define size int 50000)
(define iterations int 30)

(define* main (subr (maxeff heapy (read @globals)) () int)
  (lambda ()
    (+ (if (test-sort qsort size) 1 0)
       (if (test-sort qsort2 size) 1 0))))

(define* run (subr (maxeff heapy (read @globals)) (int int) int)
  (lambda (i result) (if (= i 0) result (run (- i 1) (+ result (main))))))
(run iterations 0)
