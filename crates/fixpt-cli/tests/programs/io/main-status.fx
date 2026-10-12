; `main` runs after the forms, its result's low byte the status: 300, so 44.
(define main (subr (io stdout) () int)
  (lambda () (begin (write-out "in main\n") 300)))
