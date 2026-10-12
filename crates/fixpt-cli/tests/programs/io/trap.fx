; A run that fails exits 70, its message on the standard error, after what was written.
(define main (subr (io stdout) () int)
  (lambda () (begin (write-out "before\n") (car (the (listof int @heap) nil)))))
