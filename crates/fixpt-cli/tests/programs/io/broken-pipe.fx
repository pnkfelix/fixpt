; A write to a pipe no one reads fails as a value, `broken-pipe`, which the
; program sees and answers: status 3, whether the first write fails or a
; later one.
(define line string "xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx\n")
(define said (subr (io stderr) (io-error) unit)
  (lambda (e)
    (let ((what (tagcase (extract e kind) (broken-pipe u "broken pipe: ") (else k "other: "))))
      (tagcase (write-err (string-append what (string-append (extract e detail) "\n")))
        (done u #u)
        (failed f #u)))))
;; How many writes it made before one failed, and that one.
(define* spam (subr (maxeff (io stdout) (io stderr) (read (globals line said)) spin) (int) int)
  (lambda (n)
    (tagcase (write-out line)
      (done u (spam (+ n 1)))
      (failed e (begin (said e) (+ n 1))))))
(define main (subr (maxeff (read (globals line said spam)) (io stdout) (io stderr) spin) () int)
  (lambda () (if (> (spam 0) 0) 3 4)))
