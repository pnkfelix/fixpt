; Rejected: reading the clock is not sleeping (TODO.md §225): a procedure
; said to read the clock alone may not sleep until a time on it.
(define stamp (subr (io clock-read) () unit) (lambda () (sleep-until (clock))))
