;;; PARAFFINS -- Compute how many paraffins exist with N carbon atoms.
;;;
;;; From Larceny's R7RS benchmarks (test/Benchmarking/R7RS/src/paraffins.scm),
;;; ported to FX-26. Larceny's input: 10 iterations of (nb 23).
;;; Answer: 5731580.
;;;
;;; A radical, `'H` or `#(C r1 r2 r3)` in the original, is a
;;; `define-datatype` with those two variants; a paraffin, `#(BCP r1 r2)`
;;; or `#(CCP r1 r2 r3 r4)`, another. The partitions, vectors of ints,
;;; are arrays, and so are the vector of radicals by size and the pair of
;;; lists `gen` returns. Named lets are `letrec`s. `length` is written
;;; out, since FX-26's takes only a frozen list.

(define-datatype radical (H) (C radical radical radical))
(define-datatype paraffin (BCP radical radical) (CCP radical radical radical radical))
(define-type rads (listof radical @heap))
(define-type parts (listof (arrayof int @heap) @heap))
(define-type pars (listof paraffin @heap))

;;; This benchmark uses the following R6RS procedures.

(define* div (subr pure (int int) int) (lambda (x y) (quotient x y)))

;;; End of (faked) R6RS procedures.

(define* max (subr pure (int int) int) (lambda (a b) (if (< a b) b a)))
(define* odd? (subr pure (int) bool) (lambda (j) (= (modulo j 2) 1)))

(define* vector3 (subr (maxeff (alloc @heap) (write @heap)) (int int int) (arrayof int @heap))
  (lambda (a b c)
    (let ((v (the (arrayof int @heap) (make-array 3 a))))
      (begin (array-set! v 1 b) (array-set! v 2 c) v))))
(define* vector4 (subr (maxeff (alloc @heap) (write @heap)) (int int int int) (arrayof int @heap))
  (lambda (a b c d)
    (let ((v (the (arrayof int @heap) (make-array 4 a))))
      (begin (array-set! v 1 b) (array-set! v 2 c) (array-set! v 3 d) v))))

(define* three-partitions (subr (maxeff (alloc @heap) (write @heap) spin) (int) parts)
  (lambda (m)
    (letrec ((loop1 (subr (maxeff (alloc @heap) (write @heap) spin (read (globals div vector3))) (parts int) parts)
               (lambda (lst nc1)
                 (if (< nc1 0)
                     lst
                     (letrec ((loop2 (subr (maxeff (alloc @heap) (write @heap) spin (read (globals div vector3))) (parts int) parts)
                                (lambda (lst nc2)
                                  (if (< nc2 nc1)
                                      (loop1 lst
                                             (- nc1 1))
                                      (loop2 (cons (vector3 nc1 nc2 (- m (+ nc1 nc2))) lst)
                                             (- nc2 1))))))
                       (loop2 lst (div (- m nc1) 2)))))))
      (loop1 nil (div m 3)))))

(define* four-partitions (subr (maxeff (alloc @heap) (write @heap) spin) (int) parts)
  (lambda (m)
    (letrec ((loop1 (subr (maxeff (alloc @heap) (write @heap) spin (read (globals div max vector4))) (parts int) parts)
               (lambda (lst nc1)
                 (if (< nc1 0)
                     lst
                     (letrec ((loop2 (subr (maxeff (alloc @heap) (write @heap) spin (read (globals div max vector4))) (parts int) parts)
                                (lambda (lst nc2)
                                  (if (< nc2 nc1)
                                      (loop1 lst
                                             (- nc1 1))
                                      (let ((start (max nc2 (- (div (+ m 1) 2) (+ nc1 nc2)))))
                                        (letrec ((loop3 (subr (maxeff (alloc @heap) (write @heap) spin (read (globals div max vector4))) (parts int) parts)
                                                   (lambda (lst nc3)
                                                     (if (< nc3 start)
                                                         (loop2 lst (- nc2 1))
                                                         (loop3 (cons (vector4 nc1 nc2 nc3 (- m (+ nc1 (+ nc2 nc3)))) lst)
                                                                (- nc3 1))))))
                                          (loop3 lst (div (- m (+ nc1 nc2)) 2))))))))
                       (loop2 lst (div (- m nc1) 3)))))))
      (loop1 nil (div m 4)))))

;; What `gen`'s loops do: walk and build the lists, and read the globals
;; they call.
(define-effect gens
  (maxeff (read @heap) (write @heap) (alloc @heap) spin
          (read (globals C BCP CCP div max odd? vector3 vector4 three-partitions four-partitions))))

(define* gen (subr gens (int) (arrayof pars @heap))
  (lambda (n)
    (let* ((n/2 (div n 2))
           (radicals (the (arrayof rads @heap) (make-array (+ n/2 1) (cons (H) nil)))))
      (letrec ((rads-of-size (subr gens (int) rads)
                 (lambda (n)
                   (letrec ((loop1 (subr gens (parts rads) rads)
                              (lambda (ps lst)
                                (if (null? ps)
                                    lst
                                    (let* ((p (car ps))
                                           (nc1 (array-ref p 0))
                                           (nc2 (array-ref p 1))
                                           (nc3 (array-ref p 2)))
                                      (letrec ((loop2 (subr gens (rads rads) rads)
                                                 (lambda (rads1 lst)
                                                   (if (null? rads1)
                                                       lst
                                                       (letrec ((loop3 (subr gens (rads rads) rads)
                                                                  (lambda (rads2 lst)
                                                                    (if (null? rads2)
                                                                        lst
                                                                        (letrec ((loop4 (subr gens (rads rads) rads)
                                                                                   (lambda (rads3 lst)
                                                                                     (if (null? rads3)
                                                                                         lst
                                                                                         (cons (C (car rads1)
                                                                                                  (car rads2)
                                                                                                  (car rads3))
                                                                                               (loop4 (cdr rads3)
                                                                                                      lst))))))
                                                                          (loop4 (if (= nc2 nc3)
                                                                                     rads2
                                                                                     (array-ref radicals nc3))
                                                                                 (loop3 (cdr rads2)
                                                                                        lst)))))))
                                                         (loop3 (if (= nc1 nc2)
                                                                    rads1
                                                                    (array-ref radicals nc2))
                                                                (loop2 (cdr rads1)
                                                                       lst)))))))
                                        (loop2 (array-ref radicals nc1)
                                               (loop1 (cdr ps)
                                                      lst))))))))
                     (loop1 (three-partitions (- n 1))
                            nil))))

               (bcp-generator (subr gens (int) pars)
                 (lambda (j)
                   (if (odd? j)
                       nil
                       (letrec ((loop1 (subr gens (rads pars) pars)
                                  (lambda (rads1 lst)
                                    (if (null? rads1)
                                        lst
                                        (letrec ((loop2 (subr gens (rads pars) pars)
                                                   (lambda (rads2 lst)
                                                     (if (null? rads2)
                                                         lst
                                                         (cons (BCP (car rads1)
                                                                    (car rads2))
                                                               (loop2 (cdr rads2)
                                                                      lst))))))
                                          (loop2 rads1
                                                 (loop1 (cdr rads1)
                                                        lst)))))))
                         (loop1 (array-ref radicals (div j 2))
                                nil)))))

               (ccp-generator (subr gens (int) pars)
                 (lambda (j)
                   (letrec ((loop1 (subr gens (parts pars) pars)
                              (lambda (ps lst)
                                (if (null? ps)
                                    lst
                                    (let* ((p (car ps))
                                           (nc1 (array-ref p 0))
                                           (nc2 (array-ref p 1))
                                           (nc3 (array-ref p 2))
                                           (nc4 (array-ref p 3)))
                                      (letrec ((loop2 (subr gens (rads pars) pars)
                                                 (lambda (rads1 lst)
                                                   (if (null? rads1)
                                                       lst
                                                       (letrec ((loop3 (subr gens (rads pars) pars)
                                                                  (lambda (rads2 lst)
                                                                    (if (null? rads2)
                                                                        lst
                                                                        (letrec ((loop4 (subr gens (rads pars) pars)
                                                                                   (lambda (rads3 lst)
                                                                                     (if (null? rads3)
                                                                                         lst
                                                                                         (letrec ((loop5 (subr gens (rads pars) pars)
                                                                                                    (lambda (rads4 lst)
                                                                                                      (if (null? rads4)
                                                                                                          lst
                                                                                                          (cons (CCP (car rads1)
                                                                                                                     (car rads2)
                                                                                                                     (car rads3)
                                                                                                                     (car rads4))
                                                                                                                (loop5 (cdr rads4)
                                                                                                                       lst))))))
                                                                                           (loop5 (if (= nc3 nc4)
                                                                                                      rads3
                                                                                                      (array-ref radicals nc4))
                                                                                                  (loop4 (cdr rads3)
                                                                                                         lst)))))))
                                                                          (loop4 (if (= nc2 nc3)
                                                                                     rads2
                                                                                     (array-ref radicals nc3))
                                                                                 (loop3 (cdr rads2)
                                                                                        lst)))))))
                                                         (loop3 (if (= nc1 nc2)
                                                                    rads1
                                                                    (array-ref radicals nc2))
                                                                (loop2 (cdr rads1)
                                                                       lst)))))))
                                        (loop2 (array-ref radicals nc1)
                                               (loop1 (cdr ps)
                                                      lst))))))))
                     (loop1 (four-partitions (- j 1))
                            nil))))

               (loop (subr gens (int) (arrayof pars @heap))
                 (lambda (i)
                   (if (> i n/2)
                       (let ((v (the (arrayof pars @heap) (make-array 2 (bcp-generator n)))))
                         (begin (array-set! v 1 (ccp-generator n)) v))
                       (begin
                         (array-set! radicals i (rads-of-size i))
                         (loop (+ i 1)))))))
        (loop 1)))))

(define* length (subr (maxeff (read @heap) spin) (pars) int)
  (lambda (l)
    (letrec ((loop (subr (maxeff (read @heap) spin) (pars int) int)
               (lambda (l n) (if (null? l) n (loop (cdr l) (+ n 1))))))
      (loop l 0))))

(define* nb (subr (maxeff gens (read (globals gen length))) (int) int)
  (lambda (n)
    (let ((x (gen n)))
      (+ (length (array-ref x 0))
         (length (array-ref x 1))))))

;; The inputs, where no compiler can fold them (Larceny's `hide`): globals,
;; which a later definition may replace.
(define input1 int 23)
(define iterations int 10)

(define* run (subr (maxeff gens (read (globals nb))) (int int) int)
  (lambda (i result) (if (= i 0) result (run (- i 1) (nb input1)))))
(run iterations 0)
