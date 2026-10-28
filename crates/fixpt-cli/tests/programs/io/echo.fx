; The standard input, a line at a time (TODO.md §84): each line written back
; numbered, its ending left off; a line not UTF-8 a failure the program
; sees, `invalid-data`; at the end, the count of lines, which is the status.
(define-type line-result (oneof (line string) (eof unit) (failed io-error)))
(define said (subr (io stdout) (int string) unit)
  (lambda (n s)
    (tagcase (write-out (string-append (int->string n) (string-append ": " (string-append s "\n"))))
      (done u #u)
      (failed e #u))))
(define* echo (subr (maxeff (io stdin) (io stdout) (read (globals said)) spin) (int) int)
  (lambda (n)
    (tagcase (the line-result (read-line))
      (line s (begin (said n s) (echo (+ n 1))))
      (eof u n)
      (failed e
        (begin (said n (tagcase (extract e kind) (invalid-data u "bad") (else k "?")))
               (echo (+ n 1)))))))
(define main (subr (maxeff (io stdin) (io stdout) spin (read (globals echo said))) () int)
  (lambda () (echo 0)))
