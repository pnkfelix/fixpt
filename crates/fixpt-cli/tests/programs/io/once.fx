; Each form runs once (TODO.md §96): a definition that writes, an
; expression that writes, a process spawned by a definition, and a form
; after them all, as every machine runs them, the evaluator written in
; FX-26 too, which once ran every definition again with each later form.
(define* said (subr (io stdout) (string) unit)
  (lambda (s) (tagcase (write-out (string-append s "\n")) (done u #u) (failed e #u))))
(define x int (begin (said "define x") 1))
(said "an expression")
(define answer (icell int @c) (make-icell))
(define p (addr int @p)
  (spawn (box int r) (begin (said "the process") (icell-put! answer (+ x (receive box))))))
(send p 41)
(define main (subr (maxeff (io stdout) (await @c) (read (globals said answer))) () int)
  (lambda () (begin (said "main") (icell-get answer))))
