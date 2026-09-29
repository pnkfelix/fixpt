;;; VECTOR-REV -- reversing a vector of 200000 integers twice, by tabulate.
;;;
;;; Written by Stephen Weeks (sweeks@sweeks.com).
;;; From MLton's benchmark suite (benchmark/tests/vector-rev.sml, commit
;;; aa2fd1ad9b91), ported to FX-26. Iteration count (ours; MLton's driver
;;; was not fetched): a loop from 100 down to -1, 101 double reversals.
;;; (The original's doit n counts down from n * 1000; even n = 1 is 1001
;;; double reversals, some 13 s here, so the count is taken as is.)
;;; Answer: 0, element 0 of (rev (rev v)) (the original checks for it).
;;; SML's vectors are arrays; Vector.tabulate is written here.

(define-type ints (arrayof int @v))

(define* tabulate (subr (maxeff (alloc @v) (write @v) (read @v) spin) (int (subr (read @v) (int) int)) ints)
  (lambda (n f)
    (let ((v (the ints (make-array n 0))))
      (letrec ((fill (subr (maxeff (write @v) (read @v) spin) (int) unit)
                 (lambda (i) (if (< i n) (begin (array-set! v i (f i)) (fill (+ i 1))) #u))))
        (begin (fill 0) v)))))

(define* rev (subr (maxeff (alloc @v) (write @v) (read @v) spin) (ints) ints)
  (lambda (v)
    (let ((n (array-length v)))
      (tabulate n (lambda (i) (array-ref v (- (- n 1) i)))))))

;; The inputs, where no compiler can fold them: globals, which a later
;; definition may replace.
(define size int 200000)
(define iterations int 100)

(define* doit (subr (maxeff (alloc @v) (write @v) (read @v) spin) (int) int)
  (lambda (n)
    (let ((v (tabulate size (lambda (i) i))))
      (letrec ((loop (subr (maxeff (alloc @v) (write @v) (read @v) spin (read (globals rev tabulate))) (int int) int)
                 (lambda (n result)
                   (if (< n 0)
                       result
                       (loop (- n 1) (array-ref (rev (rev v)) 0))))))
        (loop n -1)))))
(doit iterations)
