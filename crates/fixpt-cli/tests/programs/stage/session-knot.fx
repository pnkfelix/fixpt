;; Knots through a session's own globals, refused as at the top level
;; (`Checker::no_reaching_itself`): `tbl` holds a procedure, `f` calls what
;; it holds, and `tbl` is defined again to hold `f`; `h` calls `g`, and `g`,
;; reading any global, is defined again to call `h`. `(f)` then ends.
(define api (module (define base 10)))
(define-type api-type (moduleof (val base int)))
(define s (sessionof api-type @heap) (make-session api))
(define line (subr (io stdout) (string) unit)
  (lambda (x) (begin (write-out (string-append x "\n")) #u)))
(define step
  (subr (maxeff stage spin (io stdout) (read @heap) (write @heap) (read @globals))
        (datum) int)
  (lambda (code)
    (session-check s (maxeff (read @globals) (io stdout)) int code
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
      (step '(define f (subr (read @globals) () int) (lambda () ((extract tbl p)))))
      (step '(define tbl (productof (p (subr (read @globals) () int))) (product (p f))))
      (step '(define g (subr (read @globals) () int) (lambda () 0)))
      (step '(define h (subr (read @globals) () int) (lambda () (g))))
      (step '(define g (subr (read @globals) () int) (lambda () (h))))
      (step '(f)))))
