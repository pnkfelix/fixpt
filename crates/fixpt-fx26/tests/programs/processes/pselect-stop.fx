;; => 60
;; A process that sums the messages it receives until it is told to stop,
;; by an I-cell, then answers with the sum: `pselect` over its mailbox and
;; the cell. The mailbox's arm comes first, so a message already there is
;; taken before the stop, and every message is sent before the stop is.
(define stop (icell unit @c) (make-icell))
(define total (icell int @c) (make-icell))
(define summer (addr int @p)
  (spawn (box int r)
    (letrec ((loop (subr (maxeff (receive r) (await @c) (init @c) nondet spin) (int) unit)
               (lambda (n)
                 (pselect ((receive box) m (loop (+ n m)))
                         ((icell-get stop) u (icell-put! total n))))))
      (loop 0))))
(send summer 10)
(send summer 20)
(send summer 30)
(icell-put! stop #u)
(icell-get total)
