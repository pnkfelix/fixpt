;; A session's steps that load files (`docs/research/eval.md`, "Decided
;; (the user's, 2026-11-26)"): each file a module of the session's own,
;; made from its text as the step is checked, never the program's; every
;; load of a path in the session one module, as in a program, so that a
;; later step's load of it is the earlier's; from the session's directory,
;; the program's until `session-directory!` says another.
(define api (module (define one int 1)))
(define-type api-type (moduleof (val one int)))
(define s (sessionof api-type @heap) (make-session api))
(define-effect sessioning (maxeff stage spin (read @heap) (write @heap) (read (globals s message))))
(define message (subr pure (stage-failure) string) (lambda (why) (extract why message)))
(define form (subr sessioning (datum) string)
  (lambda (code)
    (session-check s spin int code
      (c (tagcase c
           (expression p (int->string (p)))
           (definition d
             (tagcase (session-commit! s d (sum shadow #u))
               (defined n (string-append "defined " n))
               (failed why (string-append "not defined: " (message why)))))))
      (why (string-append "refused: " (message why))))))
(define line (subr (io stdout) (string) unit)
  (lambda (x) (begin (write-out (string-append x "\n")) #u)))
(define main
  (subr (maxeff sessioning (io stdout) (read (globals form line))) () int)
  (lambda ()
    (begin
      (line (form '(define lib (load-module "loads/lib.fx"))))
      (line (form '(with lib (double 21))))
      ;; Loaded again in a later step: the same module, its `id` the same.
      (line (form '(let ((l (load-module "loads/lib.fx")))
                     ((with l doubled-id) ((with lib base::make-id) 2)))))
      (line (form '(let ((m (load-module "loads/missing.fx"))) 1)))
      (session-directory! s "loads")
      (line (form '(let ((b (load-module "base.fx"))) ((with b id-number) ((with b make-id) 9)))))
      0)))
