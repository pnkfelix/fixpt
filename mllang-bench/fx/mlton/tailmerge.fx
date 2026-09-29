;;; TAILMERGE -- merging two sorted lists of 100000 integers, tail-recursively,
;;; into an accumulator that is then reversed onto the rest.
;;;
;;; Written by Stephen Weeks (sweeks@sweeks.com).
;;; From MLton's benchmark suite (benchmark/tests/tailmerge.sml, commit
;;; aa2fd1ad9b91), ported to FX-26. Iteration count (ours; MLton's driver
;;; was not fetched): (doit 200), merging the same two lists 200 times.
;;; Answer: 0, the head of the merged list (the original checks for it).
;;; SML's List.tabulate is written here, building the list from its end.

(define-type ints (listof int @l))

(define* tabulate (subr (maxeff (alloc @l) spin) (int (subr pure (int) int)) ints)
  (lambda (n f)
    (letrec ((build (subr (maxeff (alloc @l) spin) (int ints) ints)
               (lambda (i acc) (if (< i 0) acc (build (- i 1) (cons (f i) acc))))))
      (build (- n 1) nil))))

(define* merge (subr (maxeff (read @l) (alloc @l) spin) (ints ints) ints)
  (lambda (l1 l2)
    (letrec ((revapp (subr (maxeff (read @l) (alloc @l) spin) (ints ints) ints)
               (lambda (l acc)
                 (if (null? l) acc (revapp (cdr l) (cons (car l) acc)))))
             (loop (subr (maxeff (read @l) (alloc @l) spin) (ints ints ints) ints)
               (lambda (l1 l2 acc)
                 (cond ((null? l1) (revapp acc l2))
                       ((null? l2) (revapp acc l1))
                       (else
                        (let ((x1 (car l1)) (x2 (car l2)))
                          (if (<= x1 x2)
                              (loop (cdr l1) l2 (cons x1 acc))
                              (loop l1 (cdr l2) (cons x2 acc)))))))))
      (loop l1 l2 nil))))

;; The inputs, where no compiler can fold them: globals, which a later
;; definition may replace.
(define len int 100000)
(define iterations int 200)

(define* doit (subr (maxeff (read @l) (alloc @l) spin) (int) int)
  (lambda (size)
    (let ((l1 (tabulate len (lambda (i) (* i 2))))
          (l2 (tabulate len (lambda (i) (+ (* i 2) 1)))))
      (letrec ((loop (subr (maxeff (read @l) (alloc @l) spin (read (globals merge))) (int int) int)
                 (lambda (n result)
                   (if (= n 0) result (loop (- n 1) (car (merge l1 l2)))))))
        (loop size -1)))))
(doit iterations)
