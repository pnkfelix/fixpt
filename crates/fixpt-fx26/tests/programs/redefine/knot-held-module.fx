;;; The same knot through a module's value.
(define-type m-type (moduleof (val p (subr (read (globals m)) () int))))
(define m m-type (module (define p (subr pure () int) (lambda () 0))))
