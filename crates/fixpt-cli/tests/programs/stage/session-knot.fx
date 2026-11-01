;; Knots through a session's own globals, refused as at the top level
;; (`Checker::no_reaching_itself`), at their first definitions: a global
;; holding a procedure that reads any global, and a procedure that does.
;; One that says `spin` is defined, and `(g)` runs.
(define api (module (define base 10)))
(define-type api-type (moduleof (val base int)))
(define s (sessionof api-type @heap) (make-session api))
(define line (subr (io stdout) (string) unit)
  (lambda (x) (begin (write-out (string-append x "\n")) #u)))
(define step
  (subr (maxeff stage spin (io stdout) (read @heap) (write @heap) (read @globals))
        (datum) int)
  (lambda (code)
    (session-check s (maxeff (read @globals) (io stdout) spin) int code
      (c (tagcase c
           (expression p (begin (line "running") (p)))
           (definition d
             (tagcase (%session-ready s d (sum shadow #u))
               (go run
                 (begin (run)
                        (tagcase (%session-committed! s d)
                          (defined n (begin (line (string-append "defined " n)) 0))
                          (failed why (begin (line (extract why message)) 2)))))
               (failed why (begin (line (extract why message)) 3))))))
      (why (begin (line (string-append "refused: " (extract why message))) 4)))))
(define main
  (subr (maxeff stage spin (io stdout) (read @heap) (write @heap) (read @globals)) () int)
  (lambda ()
    (begin
      (step '(define tbl (productof (p (subr (read @globals) () int)))
                 (product (p (lambda () 0)))))
      (step '(define g (subr (read @globals) () int) (lambda () 0)))
      (step '(define g (subr (maxeff (read @globals) spin) () int) (lambda () 0)))
      (step '(g)))))
