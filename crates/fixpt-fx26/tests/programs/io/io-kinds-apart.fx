; Rejected: one I/O effect does not cover another: a procedure that may
; write the standard error is not one that only writes the standard output.
(define say (subr (io stdout) (string) unit)
  (lambda (s) (tagcase (write-err s) (done u #u) (failed e #u))))
