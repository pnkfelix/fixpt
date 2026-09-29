;;; VECTOR -- Vector benchmark for (scheme vector).
;;;
;;; From Larceny's R7RS benchmarks (test/Benchmarking/R7RS/src/vector.scm),
;;; ported to FX-26. Larceny's input: 10 iterations of (go 8).
;;; Answer: #(#(x0 x1 x2 x3 x4 x5 x6 x7)), shown as ((x0 x1 x2 x3 x4 x5 x6
;;; x7)): FX-26 prints no array, so the last form makes the result, a
;;; vector of vectors, lists (once, after the iterations).
;;;
;;; Vectors are arrays. FX-26 has no (scheme vector), so the SRFI 133
;;; procedures the benchmark calls are written here, after Larceny's own
;;; (the reference implementation, lib/SRFI/srfi/133.body.scm), each for
;;; the element types it is used at:
;;; - `vector-unfold` with one seed, `vector-map` with one vector,
;;;   `vector-index` with one vector, as their fast paths;
;;; - `vector-append` and `vector-concatenate` as `vector-concatenate:aux`
;;;   (the lengths added up, then each copied in), `vector-append` of two;
;;; - `vector-append-subvectors` of two and of three subvectors, the total
;;;   length and then each subvector copied in, without the variadic
;;;   version's lists of arguments. The one of three takes only the four
;;;   values its one call varies, not nine arguments: FX-26's native
;;;   convention takes at most eight, and a procedure of more runs as
;;;   cellular code, as does every procedure that calls it;
;;; - `vector-partition` counts with `vector-count` first, as there, so the
;;;   predicate runs twice on each element.
;;; `make-vector`'s unspecified fill is a value of the element type.
;;; `equal?` on vectors of symbols is written out.

(define-type ints (arrayof int @heap))
(define-type strs (arrayof string @heap))
(define-type symv (arrayof symbol @heap))
(define-type setv (arrayof symv @heap))
(define-type setvv (arrayof setv @heap))
(define-effect vecs (maxeff (read @heap) (write @heap) (alloc @heap) spin))

(define empty symv (make-array 0 'ignored))

;; (%vector-copy! target tstart source sstart send), left to right.
(define* copy-syms! (subr vecs (symv int symv int int) unit)
  (lambda (target tstart source sstart send)
    (if (< sstart send)
        (begin (array-set! target tstart (array-ref source sstart))
               (copy-syms! target (+ tstart 1) source (+ sstart 1) send))
        #u)))

(define* copy-sets! (subr vecs (setv int setv int int) unit)
  (lambda (target tstart source sstart send)
    (if (< sstart send)
        (begin (array-set! target tstart (array-ref source sstart))
               (copy-sets! target (+ tstart 1) source (+ sstart 1) send))
        #u)))

;; (vector-append-subvectors v1 s1 e1 v2 s2 e2)
(define* append-subvectors2 (subr vecs (symv int int symv int int) symv)
  (lambda (v1 s1 e1 v2 s2 e2)
    (let ((result (the symv (make-array (+ (- e1 s1) (- e2 s2)) 'ignored))))
      (begin (copy-syms! result 0 v1 s1 e1)
             (copy-syms! result (- e1 s1) v2 s2 e2)
             result))))

;; (vector-append-subvectors perm 0 i universe j (+ j 1) perm i (vector-length perm)),
;; the one call of three subvectors, given perm, i, universe and j: a
;; procedure of nine parameters runs only as cellular code (see above).
(define* append-subvectors3 (subr vecs (symv int symv int) symv)
  (lambda (perm i universe j)
    (let* ((v1 perm) (s1 0) (e1 i)
           (v2 universe) (s2 j) (e2 (+ j 1))
           (v3 perm) (s3 i) (e3 (array-length perm))
           (result (the symv (make-array (+ (- e1 s1) (+ (- e2 s2) (- e3 s3))) 'ignored))))
      (begin (copy-syms! result 0 v1 s1 e1)
             (copy-syms! result (- e1 s1) v2 s2 e2)
             (copy-syms! result (+ (- e1 s1) (- e2 s2)) v3 s3 e3)
             result))))

;; vector-concatenate:aux, for a list of vectors of subsets.
(define* concatenate-sets (subr vecs ((listof setv @heap)) setv)
  (lambda (vectors)
    (letrec ((compute-length (subr vecs ((listof setv @heap) int) int)
               (lambda (vectors len)
                 (if (null? vectors)
                     len
                     (compute-length (cdr vectors) (+ (array-length (car vectors)) len)))))
             (concatenate! (subr (maxeff vecs (read (globals copy-sets!))) ((listof setv @heap) setv int) setv)
               (lambda (vectors target to)
                 (if (null? vectors)
                     target
                     (let* ((vec1 (car vectors))
                            (len (array-length vec1)))
                       (begin (copy-sets! target to vec1 0 len)
                              (concatenate! (cdr vectors) target (+ to len))))))))
      (cond ((null? vectors) (the setv (make-array 0 empty)))
            ((null? (cdr vectors))
             ;; Blech, we still have to allocate a new one.
             (let* ((vec (car vectors))
                    (len (array-length vec))
                    (new (the setv (make-array len empty))))
               (begin (copy-sets! new 0 vec 0 len) new)))
            (else (concatenate! vectors
                                (make-array (compute-length vectors 0) empty)
                                0))))))

;; (vector-append a b), through vector-concatenate:aux.
(define* vector-append (subr vecs (setv setv) setv)
  (lambda (a b) (concatenate-sets (cons a (cons b nil)))))

(define* vector->list (subr vecs (setvv) (listof setv @heap))
  (lambda (v)
    (letrec ((loop (subr vecs (int (listof setv @heap)) (listof setv @heap))
               (lambda (i l) (if (< i 0) l (loop (- i 1) (cons (array-ref v i) l))))))
      (loop (- (array-length v) 1) nil))))

;; equal? on vectors of symbols.
(define* symv=? (subr vecs (symv symv) bool)
  (lambda (a b)
    (letrec ((loop (subr vecs (int) bool)
               (lambda (i)
                 (cond ((= i (array-length a)) #t)
                       ((symbol=? (array-ref a i) (array-ref b i)) (loop (+ i 1)))
                       (else #f)))))
      (and (= (array-length a) (array-length b)) (loop 0)))))

(define* symbols (subr vecs (int) symv)
  (lambda (n)
    (let ((iv (the ints (make-array n 0))))
      (letrec ((unfold1! (subr vecs (int int) unit)
                 (lambda (i seed)
                   (if (< i n)
                       ;; (lambda (i x) (values i x))
                       (begin (array-set! iv i i) (unfold1! (+ i 1) seed))
                       #u)))
               (map-number->string (subr vecs (strs int) strs)
                 (lambda (new i)
                   (if (< i n)
                       (begin (array-set! new i (int->string (array-ref iv i)))
                              (map-number->string new (+ i 1)))
                       new)))
               (map-prefix (subr vecs (strs strs int) strs)
                 (lambda (old new i)
                   (if (< i n)
                       (begin (array-set! new i (string-append "x" (array-ref old i)))
                              (map-prefix old new (+ i 1)))
                       new)))
               (map-string->symbol (subr vecs (strs symv int) symv)
                 (lambda (old new i)
                   (if (< i n)
                       (begin (array-set! new i (string->symbol (array-ref old i)))
                              (map-string->symbol old new (+ i 1)))
                       new))))
        (begin
          (unfold1! 0 0)
          (map-string->symbol
           (map-prefix (map-number->string (make-array n "") 0) (make-array n "") 0)
           (make-array n 'ignored)
           0))))))

(define* powerset (subr vecs (symv) setv)
  (lambda (universe)
    (letrec ((ps (subr (maxeff vecs (read (globals append-subvectors2 copy-syms! vector-append concatenate-sets copy-sets! empty))) (int) setv)
               (lambda (j)
                 (if (= j (array-length universe))
                     (the setv (make-array 1 empty))
                     (let* ((x (array-ref universe j))
                            (pu2 (ps (+ j 1)))
                            (mapped (the setv (make-array (array-length pu2) empty))))
                       (letrec ((map1! (subr (maxeff vecs (read (globals append-subvectors2 copy-syms!))) (int) setv)
                                  (lambda (i)
                                    (if (< i (array-length pu2))
                                        (let ((y (array-ref pu2 i)))
                                          (begin
                                            (array-set! mapped i
                                                        (append-subvectors2 universe j (+ j 1) y 0 (array-length y)))
                                            (map1! (+ i 1))))
                                        mapped))))
                         (vector-append pu2 (map1! 0))))))))
      (ps 0))))

(define* permutations (subr vecs (symv) setv)
  (lambda (universe)
    (letrec ((permutations
              (subr (maxeff vecs (read (globals append-subvectors3 copy-syms! vector->list concatenate-sets copy-sets! empty))) (int) setv)
               (lambda (j)
                 (if (= j (array-length universe))
                     (the setv (make-array 1 empty))
                     (let* ((x (array-ref universe j))
                            (perms2 (permutations (+ j 1)))
                            (outer (the setvv (make-array (array-length perms2) (make-array 0 empty)))))
                       (letrec ((map-perm! (subr (maxeff vecs (read (globals append-subvectors3 copy-syms! empty))) (int) setvv)
                                  (lambda (k)
                                    (if (< k (array-length perms2))
                                        (let* ((perm (array-ref perms2 k))
                                               (n (array-length perm))
                                               (is (the ints (make-array (+ n 1) 0)))
                                               (new (the setv (make-array (+ n 1) empty))))
                                          (letrec ((unfold1! (subr vecs (int int) unit)
                                                     (lambda (i seed)
                                                       (if (< i (+ n 1))
                                                           ;; (lambda (i seed) (values seed (+ seed 1)))
                                                           (begin (array-set! is i seed) (unfold1! (+ i 1) (+ seed 1)))
                                                           #u)))
                                                   (map-i! (subr (maxeff vecs (read (globals append-subvectors3 copy-syms!))) (int) setv)
                                                     (lambda (m)
                                                       (if (< m (+ n 1))
                                                           (let ((i (array-ref is m)))
                                                             (begin
                                                               (array-set! new m
                                                                           (append-subvectors3 perm i universe j))
                                                               (map-i! (+ m 1))))
                                                           new))))
                                            (begin (unfold1! 0 0)
                                                   (array-set! outer k (map-i! 0))
                                                   (map-perm! (+ k 1)))))
                                        outer))))
                         (concatenate-sets (vector->list (map-perm! 0)))))))))
      (permutations 0))))

(define* go (subr vecs (int) setv)
  (lambda (n)
    (let* ((universe (symbols n))
           (subsets (powerset universe))
           (perms (permutations universe)))
      (letrec ((vector-index (subr (maxeff vecs (read (globals symv=?))) (symv int) bool)
                 ;; (vector-index (lambda (v) (equal? v perm)) subsets),
                 ;; #t where it returns an index
                 (lambda (perm i)
                   (cond ((= i (array-length subsets)) #f)
                         ((symv=? (array-ref subsets i) perm) #t)
                         (else (vector-index perm (+ i 1))))))
               (vector-count (subr (maxeff vecs (read (globals symv=?))) (int int) int)
                 (lambda (i count)
                   (if (= i (array-length perms))
                       count
                       (vector-count (+ i 1) (if (vector-index (array-ref perms i) 0) (+ count 1) count)))))
               (partition (subr (maxeff vecs (read (globals symv=?))) (setv int int int) setv)
                 (lambda (result i yes no)
                   (if (= i (array-length perms))
                       result
                       (let ((elem (array-ref perms i)))
                         (if (vector-index elem 0)
                             (begin (array-set! result yes elem)
                                    (partition result (+ i 1) (+ yes 1) no))
                             (begin (array-set! result no elem)
                                    (partition result (+ i 1) yes (+ no 1)))))))))
        (let* ((cnt (vector-count 0 0))
               (v (partition (make-array (array-length perms) empty) 0 0 cnt))
               (copy (the setv (make-array cnt empty))))
          ;; (vector-copy v 0 n)
          (begin (copy-sets! copy 0 v 0 cnt) copy))))))

;; The inputs, where no compiler can fold them (Larceny's `hide`): globals,
;; which a later definition may replace.
(define input1 int 8)
(define iterations int 10)

(define* run (subr vecs (int setv) setv)
  (lambda (i result) (if (= i 0) result (run (- i 1) (go input1)))))

;; The result, a vector of vectors, as a list of lists, to be shown.
(define* lists (subr vecs (setv int) (listof (listof symbol @heap) @heap))
  (lambda (v i)
    (letrec ((row (subr vecs (symv int) (listof symbol @heap))
               (lambda (w k) (if (= k (array-length w)) nil (cons (array-ref w k) (row w (+ k 1)))))))
      (if (= i (array-length v)) (the (listof (listof symbol @heap) @heap) nil) (the (listof (listof symbol @heap) @heap) (cons (row (array-ref v i) 0) (lists v (+ i 1))))))))
(lists (run iterations (make-array 0 empty)) 0)
