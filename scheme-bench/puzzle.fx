;;; PUZZLE -- Forest Baskett's Puzzle benchmark, originally written in Pascal.
;;;
;;; From Larceny's R7RS benchmarks (test/Benchmarking/R7RS/src/puzzle.scm),
;;; ported to FX-26. Larceny's input: 1000 iterations of (start 511).
;;; Answer: 2005.
;;;
;;; Vectors are arrays; `(make-vector n)`, whose elements are unspecified,
;;; is `(make-array n #f)`, or of 0 for vectors of integers. The globals
;;; the benchmark assigns (`*iii*`, `*kount*`) and the local variables it
;;; assigns (`trial`'s `k`, `definePiece`'s `index`) are references. The
;;; `do` loops are local `letrec` loops, an inner loop taking the outer
;;; loops' counters as arguments; `call-with-current-continuation` is
;;; `cwcc`, its continuation in the region `@ret`. `start` returns -1 where
;;; Larceny's returns #f (it never does), and the branch that would display
;;; "Error." (it never runs) does nothing, since FX-26 has no output.
;;; `(zero? n)` is `(= n 0)`. The final `for-each` making `*p*`'s rows is
;;; `init-p`, run before the benchmark.

(define-type bvec (arrayof bool @heap))
(define-type ivec (arrayof int @heap))
(define-type ints (listof int @heap))

(define* my-iota (subr (maxeff (alloc @heap) spin) (int) ints)
  (lambda (n)
    (letrec ((loop (subr (maxeff (alloc @heap) spin) (int ints) ints)
               (lambda (n list)
                 (if (= n 0)
                     list
                     (loop (- n 1) (cons (- n 1) list))))))
      (loop n nil))))

(define size int 511)
(define classmax int 3)
(define typemax int 12)

(define *iii* (ref int @heap) (new 0))
(define *kount* (ref int @heap) (new 0))
(define *d* int 8)

(define *piececount* ivec (make-array (+ classmax 1) 0))
(define *class* ivec (make-array (+ typemax 1) 0))
(define *piecemax* ivec (make-array (+ typemax 1) 0))
(define *puzzle* bvec (make-array (+ size 1) #f))
(define *p* (arrayof bvec @heap) (make-array (+ typemax 1) (the bvec (make-array 0 #f))))

(define* fit (subr (maxeff (read @heap) spin) (int int) bool)
  (lambda (i j)
    (let ((end (array-ref *piecemax* i)))
      (letrec ((loop (subr (maxeff (read @heap) spin (read (globals *p* *puzzle*))) (int) bool)
                 (lambda (k)
                   (if (or (> k end)
                           (and (array-ref (array-ref *p* i) k)
                                (array-ref *puzzle* (+ j k))))
                       (if (> k end) #t #f)
                       (loop (+ k 1))))))
        (loop 0)))))

(define* place (subr (maxeff (read @heap) (write @heap) spin) (int int) int)
  (lambda (i j)
    (let ((end (array-ref *piecemax* i)))
      (letrec ((mark (subr (maxeff (read @heap) (write @heap) spin (read (globals *p* *puzzle*))) (int) unit)
                 (lambda (k)
                   (if (> k end)
                       #u
                       (begin
                         (if (array-ref (array-ref *p* i) k)
                             (array-set! *puzzle* (+ j k) #t)
                             #u)
                         (mark (+ k 1))))))
               (next (subr (maxeff (read @heap) spin (read (globals size *puzzle*))) (int) int)
                 (lambda (k)
                   (if (or (> k size) (not (array-ref *puzzle* k)))
                       (if (> k size) 0 k)
                       (next (+ k 1))))))
        (begin
          (mark 0)
          (array-set! *piececount*
                      (array-ref *class* i)
                      (- (array-ref *piececount* (array-ref *class* i)) 1))
          (next j))))))

(define* puzzle-remove (subr (maxeff (read @heap) (write @heap) spin) (int int) unit)
  (lambda (i j)
    (let ((end (array-ref *piecemax* i)))
      (letrec ((unmark (subr (maxeff (read @heap) (write @heap) spin (read (globals *p* *puzzle*))) (int) unit)
                 (lambda (k)
                   (if (> k end)
                       #u
                       (begin
                         (if (array-ref (array-ref *p* i) k)
                             (array-set! *puzzle* (+ j k) #f)
                             #u)
                         (unmark (+ k 1)))))))
        (begin
          (unmark 0)
          (array-set! *piececount*
                      (array-ref *class* i)
                      (+ (array-ref *piececount* (array-ref *class* i)) 1)))))))

(define* trial (subr (maxeff (read @heap) (write @heap) (alloc @heap) (goto @ret) (comefrom @ret) spin) (int) bool)
  (lambda (j)
    (let ((k (the (ref int @heap) (new 0))))
      (cwcc
       (lambda ((return (subr (goto @ret) (bool) void)))
         (letrec ((loop (subr (maxeff (read @heap) (write @heap) (alloc @heap) (goto @ret) (comefrom @ret) spin
                                      (read (globals typemax *kount* *piececount* *class* *piecemax* *p* *puzzle* size
                                                     fit place puzzle-remove trial)))
                              (int) bool)
                    (lambda (i)
                      (if (> i typemax)
                          (begin (set *kount* (+ (get *kount*) 1)) #f)
                          (begin
                            (if (not
                                 (= (array-ref *piececount* (array-ref *class* i)) 0))
                                (if (fit i j)
                                    (begin
                                      (set k (place i j))
                                      (if (or (trial (get k)) (= (get k) 0))
                                          (begin
                                            (set *kount* (+ (get *kount*) 1))
                                            (return #t))
                                          (puzzle-remove i j)))
                                    #u)
                                #u)
                            (loop (+ i 1)))))))
           (loop 0)))))))

(define* definePiece (subr (maxeff (read @heap) (write @heap) (alloc @heap) spin) (int int int int) unit)
  (lambda (iclass ii jj kk)
    (let ((index (the (ref int @heap) (new 0))))
      (letrec ((loop-k (subr (maxeff (read @heap) (write @heap) spin (read (globals *d* *p* *iii*))) (int int int) unit)
                 (lambda (i j k)
                   (if (> k kk)
                       #u
                       (begin
                         (set index (+ i (* *d* (+ j (* *d* k)))))
                         (array-set! (array-ref *p* (get *iii*)) (get index) #t)
                         (loop-k i j (+ k 1))))))
               (loop-j (subr (maxeff (read @heap) (write @heap) spin (read (globals *d* *p* *iii*))) (int int) unit)
                 (lambda (i j)
                   (if (> j jj) #u (begin (loop-k i j 0) (loop-j i (+ j 1))))))
               (loop-i (subr (maxeff (read @heap) (write @heap) spin (read (globals *d* *p* *iii*))) (int) unit)
                 (lambda (i)
                   (if (> i ii) #u (begin (loop-j i 0) (loop-i (+ i 1)))))))
        (begin
          (loop-i 0)
          (array-set! *class* (get *iii*) iclass)
          (array-set! *piecemax* (get *iii*) (get index))
          (if (not (= (get *iii*) typemax))
              (set *iii* (+ (get *iii*) 1))
              #u))))))

(define* start (subr (maxeff (read @heap) (write @heap) (alloc @heap) (goto @ret) (comefrom @ret) spin) (int) int)
  (lambda (size)
    (letrec ((fill-puzzle (subr (maxeff (write @heap) spin (read (globals *puzzle*))) (int) unit)
               (lambda (m)
                 (if (> m size) #u (begin (array-set! *puzzle* m #t) (fill-puzzle (+ m 1))))))
             (hole-k (subr (maxeff (write @heap) spin (read (globals *puzzle* *d*))) (int int int) unit)
               (lambda (i j k)
                 (if (> k 5)
                     #u
                     (begin (array-set! *puzzle* (+ i (* *d* (+ j (* *d* k)))) #f)
                            (hole-k i j (+ k 1))))))
             (hole-j (subr (maxeff (write @heap) spin (read (globals *puzzle* *d*))) (int int) unit)
               (lambda (i j)
                 (if (> j 5) #u (begin (hole-k i j 1) (hole-j i (+ j 1))))))
             (hole-i (subr (maxeff (write @heap) spin (read (globals *puzzle* *d*))) (int) unit)
               (lambda (i)
                 (if (> i 5) #u (begin (hole-j i 1) (hole-i (+ i 1))))))
             (clear-m (subr (maxeff (read @heap) (write @heap) spin (read (globals *p*))) (int int) unit)
               (lambda (i m)
                 (if (> m size)
                     #u
                     (begin (array-set! (array-ref *p* i) m #f) (clear-m i (+ m 1))))))
             (clear-i (subr (maxeff (read @heap) (write @heap) spin (read (globals *p* typemax))) (int) unit)
               (lambda (i)
                 (if (> i typemax) #u (begin (clear-m i 0) (clear-i (+ i 1)))))))
      (begin
        (set *kount* 0)
        (fill-puzzle 0)
        (hole-i 1)
        (clear-i 0)
        (set *iii* 0)
        (definePiece 0 3 1 0)
        (definePiece 0 1 0 3)
        (definePiece 0 0 3 1)
        (definePiece 0 1 3 0)
        (definePiece 0 3 0 1)
        (definePiece 0 0 1 3)

        (definePiece 1 2 0 0)
        (definePiece 1 0 2 0)
        (definePiece 1 0 0 2)

        (definePiece 2 1 1 0)
        (definePiece 2 1 0 1)
        (definePiece 2 0 1 1)

        (definePiece 3 1 1 1)

        (array-set! *piececount* 0 13)
        (array-set! *piececount* 1 3)
        (array-set! *piececount* 2 1)
        (array-set! *piececount* 3 1)
        (let ((m (+ (* *d* (+ *d* 1)) 1))
              (n (the (ref int @heap) (new 0))))
          (begin
            (if (fit 0 m)
                (set n (place 0 m))
                #u)
            (if (trial (get n))
                (get *kount*)
                -1)))))))

(define* init-p (subr (maxeff (read @heap) (write @heap) (alloc @heap) spin) () unit)
  (lambda ()
    (letrec ((for-each (subr (maxeff (read @heap) (write @heap) (alloc @heap) spin (read (globals *p* size))) (ints) unit)
               (lambda (l)
                 (if (null? l)
                     #u
                     (begin (array-set! *p* (car l) (the bvec (make-array (+ size 1) #f)))
                            (for-each (cdr l)))))))
      (for-each (my-iota (+ typemax 1))))))
(init-p)

;; The inputs, where no compiler can fold them (Larceny's `hide`): globals,
;; which a later definition may replace.
(define input1 int 511)
(define iterations int 1000)

(define* run (subr (maxeff (read @heap) (write @heap) (alloc @heap) (goto @ret) (comefrom @ret) spin) (int int) int)
  (lambda (i result) (if (= i 0) result (run (- i 1) (start input1)))))
(run iterations 0)
