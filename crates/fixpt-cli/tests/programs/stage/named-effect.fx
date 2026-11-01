;; A stage's and a session step's effect named, not written out: a name a
;; `with` gives, and a `select` of a module's effect (Heist's, `TODO.md`
;; §211, 2): read as the module's effect, as a `subr`'s effect is, not as a
;; type (which it was, refused: "`e` is bound as a Effect, and the
;; description given is not one").
(define effs (module (define-effect user-eff (maxeff spin (read @heap)))))
(define api (module (define base 10)))
(define-type api-type (moduleof (val base int)))
(define s (sessionof api-type @heap) (make-session api))
(define-effect sessioning
  (maxeff stage spin (read @heap) (write @heap) (read (globals s effs said api))))
(define said (subr pure (stage-failure) string)
  (lambda (why) (string-append "refused: " (extract why message))))
(define in-session (subr sessioning (datum) string)
  (lambda (code)
    (with effs
      (session-check s user-eff int code
        (c (tagcase c
             (expression p (int->string (p)))
             (definition d "a definition")))
        (why (said why))))))
(define staged (subr sessioning (datum) string)
  (lambda (code)
    (stage api (select effs user-eff) int code
      (p (int->string (p)))
      (why (said why)))))
(define line (subr (io stdout) (string) unit)
  (lambda (s) (begin (write-out (string-append s "\n")) #u)))
(define main
  (subr (maxeff sessioning (io stdout) (read (globals in-session staged line))) () int)
  (lambda ()
    (begin
      (line (in-session '(+ base 1)))
      (line (staged '(+ base 2)))
      ;; The effect still holds: `(io stdout)` is beyond it.
      (line (staged '(begin (write-out "x") base)))
      0)))
