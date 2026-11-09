;; ! beyond what is expected, it has spin
;; An I-cell at `const` can never be filled, as filling it writes frozen
;; data; an await on one is dropped as pure, and leaves `spin` (TODO §224).
(define stuck (subr pure (int) int)
  (lambda (n) (let ((c (the (icell int const) (make-icell)))) (icell-get c))))
(stuck 1)
