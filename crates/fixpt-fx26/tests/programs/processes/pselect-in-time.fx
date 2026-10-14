;; => 42
;; A process that waits for a message, or for 30 s to pass: the message
;; comes first, so the deadline is never reached; nor is it waited for,
;; once the message has been taken (`tests/processes.rs`,
;; `a_deadline_passed_over_is_not_waited_for`).
(define answer (icell int @c) (make-icell))
(define waiter (addr int @p)
  (spawn (box int r)
    (pselect ((receive box) m (icell-put! answer m))
             ((sleep-until (i64+ (clock) (int->i64 30000000000))) u (icell-put! answer -1)))))
(send waiter 42)
(icell-get answer)
