;;; MERGE -- merging two sorted lists of integers, not tail-recursively.
;;;
;;; Written by Stephen Weeks (sweeks@sweeks.com).
;;; From MLton's benchmark suite (benchmark/tests/merge.sml, commit
;;; aa2fd1ad9b91), ported to FX-26. Iteration count (ours; MLton's driver
;;; was not fetched): (doit 500), merging the same two lists 500 times.
;;; Answer: 0, the head of the merged list (the original checks for it).
;;; SML's List.tabulate is written here, building the list from its end.
;;; Changed: the lists are 50000 long, not 100000. merge recurses once per
;;; element (200000 deep for the original), and the native machine's stack is
;;; a fixed 8 MB, which overflows somewhere between 100000 and 140000 frames
;;; of merge; MLton grows its stack. Half the length, twice the iterations.

(define-type ints (listof int @l))

(define* tabulate (subr (maxeff (alloc @l) spin) (int (subr pure (int) int)) ints)
  (lambda (n f)
    (letrec ((build (subr (maxeff (alloc @l) spin) (int ints) ints)
               (lambda (i acc) (if (< i 0) acc (build (- i 1) (cons (f i) acc))))))
      (build (- n 1) nil))))

(define* merge (subr (maxeff (read @l) (alloc @l) spin) (ints ints) ints)
  (lambda (l1 l2)
    (cond ((null? l1) l2)
          ((null? l2) l1)
          (else
           (let ((x1 (car l1)) (x2 (car l2)))
             (if (<= x1 x2)
                 (cons x1 (merge (cdr l1) l2))
                 (cons x2 (merge l1 (cdr l2)))))))))

;; The inputs, where no compiler can fold them: globals, which a later
;; definition may replace.
(define len int 50000)
(define iterations int 500)

(define* doit (subr (maxeff (read @l) (alloc @l) spin) (int) int)
  (lambda (size)
    (let ((l1 (tabulate len (lambda (i) (* i 2))))
          (l2 (tabulate len (lambda (i) (+ (* i 2) 1)))))
      (letrec ((loop (subr (maxeff (read @l) (alloc @l) spin (read (globals merge))) (int int) int)
                 (lambda (n result)
                   (if (= n 0) result (loop (- n 1) (car (merge l1 l2)))))))
        (loop size -1)))))
(doit iterations)
