; Writes to the standard output and error, each `(one done #u)` (TODO.md §84).
(define say (subr (maxeff (io stdout) (io stderr)) (string) int)
  (lambda (s)
    (begin
      (tagcase (write-out s) (done u 0) (failed e (begin (write-err (extract e detail)) 1)))
      (tagcase (write-err "to stderr\n") (done u 0) (failed e 1)))))
(say "hello, world\n")
