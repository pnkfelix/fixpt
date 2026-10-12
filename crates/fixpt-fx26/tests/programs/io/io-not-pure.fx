; Rejected: a procedure declared `pure` may not write to the standard output:
; its I/O effect is beyond what is declared (TODO.md §84).
(define shout (subr pure (string) unit)
  (lambda (s) (tagcase (write-out s) (done u #u) (failed e #u))))
