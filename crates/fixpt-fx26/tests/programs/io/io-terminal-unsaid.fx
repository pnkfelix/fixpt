; Rejected: raw mode is `(io terminal)`, which a procedure that says it
; only reads the standard input does not do (TODO.md §95).
(define* raw (subr (io stdin) () unit)
  (lambda () (tagcase (terminal-raw) (done u #u) (else r #u))))
