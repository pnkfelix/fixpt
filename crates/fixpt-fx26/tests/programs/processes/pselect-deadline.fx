;; => -1
;; A process that waits for a message, or for 5 ms to pass: no message is
;; sent, so the deadline is reached, and the process says so. The first
;; task waits for the answer, and, nothing else being able to run, sleeps
;; until the process's deadline.
(define answer (icell int @c) (make-icell))
(define waiter (addr int @p)
  (spawn (box int r)
    (pselect ((receive box) m (icell-put! answer m))
             ((sleep-until (i64+ (clock) (int->i64 5000000))) u (icell-put! answer -1)))))
(icell-get answer)
