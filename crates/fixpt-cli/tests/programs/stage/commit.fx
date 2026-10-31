;; A commit's initializer runs as the program calls the procedure readying
;; it gives (`session-commit!`'s `go`, here called apart), not before: its
;; output follows what the program writes between.
(define api (module (define base 10)))
(define-type api-type (moduleof (val base int)))
(define s (sessionof api-type @heap) (make-session api))
(define line (subr (io stdout) (string) unit)
  (lambda (x) (begin (write-out (string-append x "\n")) #u)))
(define main
  (subr (maxeff stage spin (io stdout) (read @heap) (write @heap) (read (globals s line))) () int)
  (lambda ()
    (session-check s (io stdout) int
                   '(define k (begin (write-out "initializer\n") (+ base 1)))
      (c (tagcase c
           (expression p 1)
           (definition d
             (tagcase (%session-ready s d (sum shadow #u))
               (go run
                 (begin (line "readied")
                        (run)
                        (tagcase (%session-committed! s d)
                          (defined n (begin (line (string-append "defined " n)) 0))
                          (failed why 2))))
               (failed why (begin (line (extract why message)) 3))))))
      (why (begin (line (extract why message)) 4)))))
