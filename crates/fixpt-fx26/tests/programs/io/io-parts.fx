; Accepted: the parts of I/O kinds that never wait (TODO.md §225): reading
; the clock, asking whether the standard input would wait, and managing
; programs without waiting on them, each within its whole. What says the
; whole still takes what does the part; the two together are the whole.
(define now (subr (io clock-read) () i64) (lambda () (clock)))
(define ready (subr (io stdin-poll) () bool) (lambda () (stdin-ready?)))
(define news (subr (io process-control) () int) (lambda () (process-news)))
(define old (subr (io clock) () i64) (lambda () (clock)))
(define nap (subr (io clock) () unit) (lambda () (sleep-until (i64+ (clock) (int->i64 1)))))
