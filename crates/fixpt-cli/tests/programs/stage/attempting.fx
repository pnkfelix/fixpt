;;; Staged code, and a session's step, that load a file whose code uses the
;;; scheduler's forms (`attempt`): checked by them as a program's load is,
;;; though the scheduler's module, loaded under it, is the staging's own
;;; (`TODO.md` §311).
(define m (module (define one int 1)))
(define staged
  (subr (maxeff stage spin nondet (io stdout) (read @globals)) (datum)
        (sumof (#:done unit) (#:failed io-error)))
  (lambda (code)
    (stage m (maxeff spin nondet) int code
      (p (write-out (string-append (int->string (p)) "\n")))
      (why (write-out (string-append "refused: " (extract why message) "\n"))))))
(staged '(let ((a (load-module "loads/attempting.fx"))) ((with a safe))))
(define s (sessionof (moduleof (val one int)) @heap) (make-session m))
(define stepped
  (subr (maxeff stage spin nondet (read @heap) (write @heap) (io stdout) (read (globals s))) (datum)
        (sumof (#:done unit) (#:failed io-error)))
  (lambda (code)
    (session-check s (maxeff spin nondet) int code
      (c (tagcase c
           (expression p (write-out (string-append (int->string (p)) "\n")))
           (definition d (write-out "a definition\n"))))
      (why (write-out (string-append "refused: " (extract why message) "\n"))))))
(stepped '(let ((a (load-module "loads/attempting.fx"))) ((with a safe))))
