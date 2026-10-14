;; => 7
;; The first task's own `pselect`, with no other task: the I-cell is never
;; filled, so the deadline, 2 ms away, is what it waits for.
(define c (icell int @c) (make-icell))
(pselect ((icell-get c) x x)
         ((sleep-until (i64+ (clock) (int->i64 2000000))) u 7))
