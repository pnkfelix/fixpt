;; ! it may not end: it waits, (await @q), on what nothing outside it sees
;; A wait on an I-cell nothing outside sees (TODO §224): masking drops the
;; `(await @q)`, and leaves `spin`, since to anything outside the wait is
;; work of unbounded length, and never ends if nothing fills the cell.
(define ask-self (subr pure (int) int)
  (lambda (n)
    (let ((c (the (icell int @q) (make-icell))))
      (begin
        (spawn (box int p) (icell-put! c (* 2 n)))
        (icell-get c)))))
(ask-self 21)
