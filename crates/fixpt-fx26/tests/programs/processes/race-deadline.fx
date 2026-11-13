;; => -1
;; A computation that never ends, raced against a deadline: a process
;; sleeps 5 ms and fills `timeout`, and the branch that waits for it wins,
;; the spinning one cancelled at its next time slice. The scheduler fires
;; what is due each time round, not only when no task can run: a branch
;; that spins, preempted, is parked and popped again, and would keep the
;; sleeper from ever waking (`TODO.md` §270). 5 ms, so that the fastest
;; machines' spinning stays under a form's step limit (20 M steps).
(define* spin-forever (subr spin (int) int) (lambda (n) (spin-forever (+ n 1))))
(define timeout (icell int @c) (make-icell))
(define start i64 (clock))
(define timer (addr int @p)
  (spawn (box int r)
    (pselect ((sleep-until (i64+ start (int->i64 5000000))) u (icell-put! timeout -1)))))
(race (spin-forever 0) (icell-get timeout))
