;; Evidence (`docs/research/eval.md`, "Evidence"): `stage` within a
;; `plambda`, checked against its effect, type and region parameters as
;; they were instantiated, given their evidence, `(given …)`.
(define api (module (define x 41)))
(define line (subr (io stdout) (string) unit)
  (lambda (s) (begin (write-out (string-append s "\n")) #u)))
(define-effect said (maxeff stage spin (io stdout) (read (globals api line))))
;; `code` staged within `e`, whatever `e` was instantiated as.
(define within
  (poly ((e effect)) (subr (maxeff said e) ((effectrep e) datum) unit))
  (plambda ((e effect))
    (lambda (er code)
      (stage api e int code
        (p (line (int->string (p))))
        (why (line (string-append "refused: " (extract why message))))
        (given er)))))
;; `code` staged at type `t`, shown by `show`.
(define at
  (poly ((t type)) (subr (maxeff said) ((typerep t) datum (subr pure (t) string)) unit))
  (plambda ((t type))
    (lambda (tr code show)
      (stage api pure t code
        (p (line (show (p))))
        (why (line (string-append "refused: " (extract why message))))
        (given tr)))))
;; Evidence made of evidence: `e` and output.
(define and-out
  (poly ((e effect)) (subr pure ((effectrep e)) (effectrep (maxeff e (io stdout)))))
  (plambda ((e effect)) (lambda (er) (reify-effect (maxeff e (io stdout)) (given er)))))
(define main
  (subr (maxeff said (read (globals within at and-out))) () int)
  (lambda ()
    (begin
      ((proj within pure) (reify-effect pure) '(+ x 1))
      ((proj within pure) (reify-effect pure) '(begin (write-out "out\n") x))
      ((proj within (io stdout)) (reify-effect (io stdout)) '(begin (write-out "out\n") x))
      ((proj within (io stdout)) ((proj and-out pure) (reify-effect pure))
                                 '(begin (write-out "joined\n") x))
      ((proj at int) (reify-type int) '(* x 2) (lambda ((n int)) (int->string n)))
      ((proj at string) (reify-type string) '"text" (lambda ((s string)) s))
      ((proj at string) (reify-type string) '(+ x 1) (lambda ((s string)) s))
      0)))
