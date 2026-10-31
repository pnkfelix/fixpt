;; Sessions in the condition-raising style (`fx26:session-conditions.fx`):
;; a redefinition raised to a handler, which answers it, refuses it, or
;; escapes to a `handle` outside, a restart; a fresh definition raises
;; nothing.
(define conditions (load-module "fx26:conditions.fx"))
(define with-handler (with conditions with-handler))
(define handle (with conditions handle))
(define sc (load-module "fx26:session-conditions.fx"))
(define commit! (with sc commit!))
(define api (module (define base 10)))
(define-type api-type (moduleof (val base int)))
(define s (sessionof api-type @heap) (make-session api))
(define line (subr (io stdout) (string) unit)
  (lambda (x) (begin (write-out (string-append x "\n")) #u)))
(define message (subr pure (stage-failure) string) (lambda (why) (extract why message)))
(define result (subr pure ((sumof (defined string) (failed stage-failure))) string)
  (lambda (r)
    (tagcase r
      (defined n (string-append "defined " n))
      (failed why (string-append "not defined: " (extract why message))))))
;; What committing does, besides the handler: the session's.
(define-effect commits
  (maxeff (read @heap) (write @heap) (read (globals commit! message result s)) spin))
;; What a handler that says what it was told does.
(define-effect telling (maxeff (io stdout) (read (globals line))))
;; `code`, a definition, committed under a handler that says what it was
;; told, and answers `decision`.
(define under (subr (maxeff stage commits (io stdout) (read (globals with-handler line)))
                    (datum session-decision) string)
  (lambda (code decision)
    (session-check s pure unit code
      (c (tagcase c
           (expression p "an expression")
           (definition d
             ((proj with-handler session-redefinition session-decision string commits telling)
              (lambda ((rd session-redefinition))
                (begin (line (string-append "redefines " (extract rd name) ": "
                                            (extract rd old) " to " (extract rd new)))
                       decision))
              (plambda ((k region))
                (lambda ((key (mark-key (subr telling (session-redefinition) session-decision) k)))
                  (result ((proj commit! api-type @heap pure k telling) s d key))))))))
      (why (string-append "refused: " (message why))))))
;; The same, under a handler that escapes, naming what it would redefine:
;; nothing committed.
(define escaping
  (subr (maxeff stage commits (read (globals with-handler handle))) (datum) string)
  (lambda (code)
    (session-check s pure unit code
      (c (tagcase c
           (expression p "an expression")
           (definition d
             ((proj handle string string (maxeff commits (read (globals with-handler))))
              (plambda ((r region))
                (lambda ((t (escape-tag string string r)))
                  ((proj with-handler session-redefinition session-decision string commits
                         (goto r))
                   (lambda ((rd session-redefinition)) (escape t (extract rd name)))
                   (plambda ((k region))
                     (lambda ((key (mark-key (subr (goto r) (session-redefinition)
                                                   session-decision)
                                             k)))
                       (result ((proj commit! api-type @heap pure k (goto r)) s d key)))))))
              (lambda ((n string)) (string-append "escaped, redefining " n))))))
      (why (string-append "refused: " (message why))))))
(define value (subr (maxeff stage commits) (datum) string)
  (lambda (code)
    (session-check s pure int code
      (c (tagcase c
           (expression p (int->string (p)))
           (definition d "a definition")))
      (why (string-append "refused: " (message why))))))
(define main
  (subr (maxeff stage commits (io stdout)
                (read (globals under escaping value line with-handler handle)))
        () int)
  (lambda ()
    (begin
      (line (under '(define a (+ base 1)) (sum refuse #u)))
      (line (value 'a))
      (line (under '(define a 20) (sum refuse #u)))
      (line (value 'a))
      (line (under '(define a 30) (sum shadow #u)))
      (line (value 'a))
      (line (escaping '(define a 40)))
      (line (value 'a))
      (line (escaping '(define b 2)))
      (line (value '(+ a b)))
      0)))
