; `exit` ends the run at once with its status, after what was written.
(define* count (subr (maxeff (io stdout) (io exit) spin) (int) int)
  (lambda (n)
    (if (= n 3)
        (exit 7)
        (begin (write-out (string-append (int->string n) "\n")) (count (+ n 1))))))
(define main (subr (maxeff (read (globals count)) (io stdout) (io exit) spin) () int)
  (lambda () (count 0)))
