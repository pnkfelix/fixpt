;; => 9999900014
;; Two processes that each loop 100,000 times, building a list in their
;; own reap and summing as they go, preempted at many of their polls while
;; the other runs and the heap is collected: what each keeps in registers
;; or frames across a preemption must be there, moved, when it goes on.
;; Each answers its sum, 4999950000, and 7 for a list built.
(define a (icell int @c) (make-icell))
(define b (icell int @c) (make-icell))
(define p (addr int @p)
  (spawn (box int r)
    (letrec ((go (subr (maxeff (alloc r) spin) (int int int (listof int r)) int)
               (lambda (i n s acc)
                 (if (= i n) (+ s (if (null? acc) 0 7)) (go (+ i 1) n (+ s i) (rcons r i acc))))))
      (icell-put! a (go 0 (receive box) 0 nil)))))
(define q (addr int @p)
  (spawn (box int r)
    (letrec ((go (subr (maxeff (alloc r) spin) (int int int (listof int r)) int)
               (lambda (i n s acc)
                 (if (= i n) (+ s (if (null? acc) 0 7)) (go (+ i 1) n (+ s i) (rcons r i acc))))))
      (icell-put! b (go 0 (receive box) 0 nil)))))
(send p 100000)
(send q 100000)
(+ (icell-get a) (icell-get b))
