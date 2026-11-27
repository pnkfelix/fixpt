;; A session's macros (`docs/research/eval.md`, "Decided (the user's,
;; 2026-11-26)"): a `define-syntax` step, committed, seen by the steps
;; after it; redefined, the steps after see the new one. And a file's
;; macros, imported from a module a step loaded (`import-with-syntax`).
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
      (line (form '(define-syntax twice (syntax-rules ((_ e) (+ e e))))))
      (line (form '(twice 21)))
      (line (form '(define four (twice 2))))
      (line (form '(+ four (twice 1))))
      (line (form '(define-syntax twice (syntax-rules ((_ e) (* (* e 2) 10))))))
      (line (form '(twice 1)))
      (line (form '(define kit (load-module "loads/macros.fx"))))
      (line (form '(import-with-syntax kit (only thrice))))
      (line (form '(thrice 5)))
      (line (form '(unless-zero 1 2)))
      0)))
