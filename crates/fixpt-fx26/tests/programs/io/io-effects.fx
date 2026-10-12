; Accepted: I/O effects (TODO.md §84) in procedures' types, combined with
; `maxeff` and with other atoms; a procedure that writes says so, and its
; caller too; one that only computes stays `pure`.
(define greet (subr (io stdout) (string) bool)
  (lambda (name)
    (tagcase (write-out (string-append "hello, " name)) (done u #t) (failed e #f))))
(define warn (subr (maxeff (io stderr) (read @r)) ((ref string @r)) unit)
  (lambda (msg) (tagcase (write-err (get msg)) (done u #u) (failed e #u))))
(define both (subr (maxeff (io stdout) (io stderr) (read (globals greet warn)) (read @r))
                   ((ref string @r)) bool)
  (lambda (msg) (begin (warn msg) (greet "world"))))
(define twice (subr pure (int) int) (lambda (n) (* 2 n)))
(define quit (subr (io exit) () int) (lambda () (exit 3)))
(define detail (subr pure (io-error) string) (lambda (e) (extract e detail)))
