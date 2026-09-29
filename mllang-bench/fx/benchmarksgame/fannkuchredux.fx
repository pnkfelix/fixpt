;;; FANNKUCHREDUX -- for every permutation of 1..n, count the flips of its
;;; prefix until 1 comes first: the maximum, and a checksum (the
;;; Computer Language Benchmarks Game's fannkuch-redux).
;;;
;;; From Sandmark's Benchmarks Game programs (benchmarks/benchmarksgame/
;;; fannkuchredux.ml, sandmark commit 5605805954a0), ported to FX-26;
;;; "Contributed by Paolo Ribeca, August 2011 (Based on the Java version by
;;; Oleg Mazurov)". The original's n is its first argument (default 7); the
;;; port's is `input` = 9. The original prints the worker numbers 0 to 31,
;;; then the checksum and "Pfannkuchen(n) = " the maximum; the port's value
;;; is checksum * 100 + maximum. Answer: 862930, for the output
;;;   012345678910111213141516171819202122232425262728293031
;;;   8629
;;;   Pfannkuchen(9) = 30
;;; (With the default n = 7, 22816, for 228 and 16; with n = 10, 7319638.)
;;;
;;; What the port changes:
;;; - `facts` holds 0! to 19!, where the original's holds 0! to 20!: 20!
;;;   does not fit FX-26's 61-bit integers, which are checked for overflow,
;;;   and nothing uses more than n! here.
;;; - The record `Perm.t` is a product of its three arrays; the pair `fr`
;;;   gives back is a product. `for` and `while` loops are local recursive
;;;   procedures; their loop variables stay refs where the original's are.
;;; - `c` has n + 1 elements, where the original's has n: the last `next`
;;;   of the last chunk (after the last permutation) reads and writes
;;;   `c.(n)`, past the end, which the original, compiled `-unsafe` as the
;;;   Benchmarks Game compiles it, does not notice. Here that element is 1,
;;;   so that `next` stops there.
;;; - `x land 1` is `x modulo 2`, and `lsl 1` is `* 2`.

(define-type ints (arrayof int @heap))
(define-type perm (productof (p ints) (pp ints) (c ints)))
(define-type result (productof (checksum int) (maxflips int)))
(define-effect fk (maxeff (read @heap) (write @heap) (alloc @heap) spin))

(define workers int 32)

(define facts ints
  (let* ((n 19)
         (res (the ints (make-array (+ n 1) 1))))
    (letrec ((loop (subr fk (int) ints)
               (lambda (i)
                 (if (<= i n)
                     (begin (array-set! res i (* i (array-ref res (- i 1)))) (loop (+ i 1)))
                     res))))
      (loop 1))))

;; Array.blit src srcpos dst dstpos len, for the one use here.
(define* blit (subr fk (ints int ints int int) unit)
  (lambda (src sp dst dp len)
    (if (> len 0)
        (begin (array-set! dst dp (array-ref src sp)) (blit src (+ sp 1) dst (+ dp 1) (- len 1)))
        #u)))

;; Setting up the permutation based on the given index
(define* setup (subr fk (int int) perm)
  (lambda (n idx0)
    (let ((res (product (p (let ((a (the ints (make-array n 0))))
                             (letrec ((init (subr fk (int) ints)
                                        (lambda (i) (if (< i n) (begin (array-set! a i i) (init (+ i 1))) a))))
                               (init 0))))
                        (pp (the ints (make-array n 1)))
                        (c (the ints (make-array (+ n 1) 1)))))
          (idx (the (ref int @heap) (new idx0))))
      (letrec ((outer (subr (maxeff fk (read (globals blit facts))) (int) perm)
                 (lambda (i)
                   (if (>= i 0)
                       (let ((d (quotient (get idx) (array-ref facts i))))
                         (begin
                           (array-set! (extract res c) i d)
                           (set idx (modulo (get idx) (array-ref facts i)))
                           (blit (extract res p) 0 (extract res pp) 0 (+ i 1))
                           (letrec ((inner (subr fk (int) unit)
                                      (lambda (j)
                                        (if (<= j i)
                                            (begin
                                              (array-set! (extract res p) j
                                                          (if (<= (+ j d) i)
                                                              (array-ref (extract res pp) (+ j d))
                                                              (array-ref (extract res pp) (- (- (+ j d) i) 1))))
                                              (inner (+ j 1)))
                                            #u))))
                             (inner 0))
                           (outer (- i 1))))
                       res))))
        (outer (- n 1))))))

;; Getting the next permutation
(define* next (subr fk (perm) unit)
  (lambda (perm)
    (let* ((p (extract perm p))
           (c (extract perm c))
           (plen (array-length p))
           (f (the (ref int @heap) (new (array-ref p 1)))))
      (begin
        (array-set! p 1 (array-ref p 0))
        (array-set! p 0 (get f))
        (let* ((i (the (ref int @heap) (new 1)))
               (aug-c (the (ref int @heap) (new (+ (array-ref c (get i)) 1)))))
          (begin
            (array-set! c (get i) (get aug-c))
            (letrec ((while (subr fk () unit)
                       (lambda ()
                         (if (> (get aug-c) (get i))
                             (begin
                               (array-set! c (get i) 0)
                               (set i (+ (get i) 1))
                               (let* ((n (array-ref p 1))
                                      (red-i (- (get i) 1)))
                                 (begin
                                   (array-set! p 0 n)
                                   (letrec ((for (subr fk (int) unit)
                                              (lambda (j)
                                                (if (<= j red-i)
                                                    (begin
                                                      (if (> plen (+ j 1)) (array-set! p j (array-ref p (+ j 1))) #u)
                                                      (for (+ j 1)))
                                                    #u))))
                                     (for 1))
                                   (if (> plen (get i))
                                       (begin (array-set! p (get i) (get f)) (set f n))
                                       #u)
                                   (set aug-c (+ (array-ref c (get i)) 1))
                                   (array-set! c (get i) (get aug-c))
                                   (while))))
                             #u))))
              (while))))))))

;; Counting the number of flips
(define* count (subr fk (perm) int)
  (lambda (perm)
    (let* ((p (extract perm p))
           (pp (extract perm pp))
           (f (the (ref int @heap) (new (array-ref p 0))))
           (res (the (ref int @heap) (new 1))))
      (begin
        (if (not (= (array-ref p (get f)) 0))
            (let* ((len (array-length p))
                   (red-len (- len 1)))
              (letrec ((copy (subr fk (int) unit)
                         (lambda (i)
                           (if (<= i red-len) (begin (array-set! pp i (array-ref p i)) (copy (+ i 1))) #u)))
                       (outer (subr fk () unit)
                         (lambda ()
                           (if (not (= (array-ref pp (get f)) 0))
                               (begin
                                 (set res (+ (get res) 1))
                                 (let ((lo (the (ref int @heap) (new 1)))
                                       (hi (the (ref int @heap) (new (- (get f) 1)))))
                                   (letrec ((inner (subr fk () unit)
                                              (lambda ()
                                                (if (< (get lo) (get hi))
                                                    (let ((t (array-ref pp (get lo))))
                                                      (begin
                                                        (array-set! pp (get lo) (array-ref pp (get hi)))
                                                        (array-set! pp (get hi) t)
                                                        (set lo (+ (get lo) 1))
                                                        (set hi (- (get hi) 1))
                                                        (inner)))
                                                    #u))))
                                     (inner)))
                                 (let* ((ff (get f))
                                        (t (array-ref pp ff)))
                                   (begin
                                     (array-set! pp ff ff)
                                     (set f t)))
                                 (outer))
                               #u))))
                (begin (copy 0) (outer))))
            #u)
        (get res)))))

(define* fr (subr fk (int int int) result)
  (lambda (n lo hi)
    (let ((p (setup n lo))
          (c (the (ref int @heap) (new 0)))
          (m (the (ref int @heap) (new 0)))
          (red-hi (- hi 1)))
      (letrec ((for (subr (maxeff fk (read (globals count next))) (int) unit)
                 (lambda (i)
                   (if (<= i red-hi)
                       (let ((r (count p)))
                         (begin
                           (set c (+ (get c) (* r (- 1 (* (modulo i 2) 2)))))
                           (if (> r (get m)) (set m r) #u)
                           (next p)
                           (for (+ i 1))))
                       #u))))
        (begin
          (for lo)
          (product (checksum (get c)) (maxflips (get m))))))))

;; The input, where no compiler can fold it: a global.
(define input int 9)

(define* main (subr fk (int) int)
  (lambda (s-n)
    (let* ((n s-n)
           (chunk-size (quotient (array-ref facts n) workers))
           (rem (modulo (array-ref facts n) workers))
           (w (the (ref (arrayof result @heap) @heap)
                   (new (make-array workers (product (checksum 0) (maxflips 0)))))))
      (letrec ((for (subr (maxeff fk (read (globals blit count facts fr next setup workers))) (int) unit)
                 (lambda (i)
                   (if (<= i (- workers 1))
                       (let* ((lo (+ (* i chunk-size) (if (< i rem) i rem)))
                              (hi (+ (+ lo chunk-size) (if (< i rem) 1 0))))
                         (begin
                           (array-set! (get w) i (fr s-n lo hi))
                           (for (+ i 1))))
                       #u)))
               (iter (subr fk (int int int) int)
                 (lambda (i c m)
                   (if (< i (array-length (get w)))
                       (let ((r (array-ref (get w) i)))
                         (iter (+ i 1) (+ c (extract r checksum))
                               (if (> m (extract r maxflips)) m (extract r maxflips))))
                       (+ (* c 100) m)))))
        (begin
          (for 0)
          (iter 0 0 0))))))
(main input)
