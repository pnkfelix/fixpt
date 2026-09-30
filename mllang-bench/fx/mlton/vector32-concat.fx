;;; VECTOR32-CONCAT -- concatenating a vector of 20000 Int32s to itself, and
;;; summing the result.
;;;
;;; Written by Stephen Weeks (sweeks@sweeks.com).
;;; From MLton's benchmark suite (benchmark/tests/vector32-concat.sml, commit
;;; aa2fd1ad9b91), ported to FX-26. Iteration count (ours; MLton's driver
;;; was not fetched): a loop from 600 down to -1, 601 concatenations.
;;; (The original's doit n counts down from n * 10000; even n = 1 is 10001
;;; concatenations, some 20 s here, so the count is taken as is.)
;;; Answer: 399980000, the sum (the original checks it against
;;; len * (len - 1)).
;;; Int32 becomes FX-26's int (61 bits); no sum here leaves Int32's range.
;;; SML's vectors are arrays; Vector.tabulate, Vector.concat (of a list of
;;; vectors) and Vector.foldl are written here.

(define-type ints (arrayof int @v))

(define* tabulate (subr (maxeff (alloc @v) (write @v) spin) (int (subr pure (int) int)) ints)
  (lambda (n f)
    (let ((v (the ints (make-array n 0))))
      (letrec ((fill (subr (maxeff (write @v) spin) (int) unit)
                 (lambda (i) (if (< i n) (begin (array-set! v i (f i)) (fill (+ i 1))) #u))))
        (begin (fill 0) v)))))

(define* concat (subr (maxeff (alloc @v) (read @v) (write @v) (read @l) spin) ((listof ints @l)) ints)
  (lambda (vs)
    (letrec ((total (subr (maxeff (read @l) spin) ((listof ints @l) int) int)
               (lambda (vs n) (if (null? vs) n (total (cdr vs) (+ n (array-length (car vs))))))))
      (let ((r (the ints (make-array (total vs 0) 0))))
        (letrec ((copy (subr (maxeff (read @v) (write @v) spin) (ints int int) int)
                   (lambda (v i at)
                     (if (< i (array-length v))
                         (begin (array-set! r at (array-ref v i)) (copy v (+ i 1) (+ at 1)))
                         at)))
                 (each (subr (maxeff (read @v) (write @v) (read @l) spin) ((listof ints @l) int) unit)
                   (lambda (vs at) (if (null? vs) #u (each (cdr vs) (copy (car vs) 0 at))))))
          (begin (each vs 0) r))))))

(define* foldl (subr (maxeff (read @v) spin) ((subr pure (int int) int) int ints) int)
  (lambda (f b v)
    (letrec ((loop (subr (maxeff (read @v) spin) (int int) int)
               (lambda (i acc) (if (< i (array-length v)) (loop (+ i 1) (f (array-ref v i) acc)) acc))))
      (loop 0 b))))

;; The inputs, where no compiler can fold them: globals, which a later
;; definition may replace.
(define len int 20000)
(define iterations int 600)

(define* doit (subr (maxeff (alloc @v) (read @v) (write @v) (alloc @l) (read @l) spin) (int) int)
  (lambda (n)
    (let ((v (tabulate len (lambda (i) i))))
      (letrec ((loop (subr (maxeff (alloc @v) (read @v) (write @v) (alloc @l) (read @l) spin
                                   (read (globals concat foldl))) (int int) int)
                 (lambda (n result)
                   (if (< n 0)
                       result
                       (loop (- n 1)
                             (foldl (lambda (x y) (+ x y)) 0
                                    (concat (list v v))))))))
        (loop n -1)))))
(doit iterations)
