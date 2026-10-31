;; Evidence in a session (`docs/research/eval.md`, "Evidence"): its steps
;; checked within a `plambda`'s effect parameter, as it was instantiated.
(define line (subr (io stdout) (string) unit)
  (lambda (s) (begin (write-out (string-append s "\n")) #u)))
(define-type api-type (moduleof (val base int)))
(define s (sessionof api-type @heap) (make-session (module (define base 10))))
(define step
  (poly ((e effect))
    (subr (maxeff stage spin e (io stdout) (read @heap) (write @heap) (read (globals s line)))
          ((effectrep e) datum) unit))
  (plambda ((e effect))
    (lambda (er code)
      (session-check s e int code
        (c (tagcase c
             (expression p (line (int->string (p))))
             (definition d
               (tagcase (session-commit! s d (sum shadow #u))
                 (defined n (line (string-append "defined " n)))
                 (failed why (line (extract why message)))))))
        (why (line (string-append "refused: " (extract why message))))
        (given er)))))
(define main
  (subr (maxeff stage spin (io stdout) (read @heap) (write @heap) (read (globals step line s)))
        () int)
  (lambda ()
    (begin
      ((proj step pure) (reify-effect pure) '(define a (+ base 1)))
      ((proj step pure) (reify-effect pure) '(+ a 1))
      ((proj step pure) (reify-effect pure) '(begin (write-out "out\n") a))
      ((proj step (io stdout)) (reify-effect (io stdout)) '(begin (write-out "out\n") a))
      ((proj step (io stdout)) (reify-effect (io stdout))
                               '(define b (begin (write-out "b\n") 2)))
      ((proj step pure) (reify-effect pure) '(+ a b))
      0)))
