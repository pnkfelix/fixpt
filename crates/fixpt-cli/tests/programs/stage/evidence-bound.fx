;; Bounds (`docs/research/eval.md`, "Evidence"): evidence of at most an effect,
;; made of exact evidence (`effect-bound`), standing for a larger one where
;; less is safe, in the effect and in a frozen list; exact evidence where
;; the variable is also taken.
(define api (module (define x 41)))
(define line (subr (io stdout) (string) unit)
  (lambda (s) (begin (write-out (string-append s "\n")) #u)))
(define-effect said (maxeff stage spin (io stdout) (read (globals api line))))
;; Within at most `e`.
(define within
  (poly ((e effect)) (subr (maxeff said e) ((effectbound e) datum) unit))
  (plambda ((e effect))
    (lambda (eb code)
      (stage api e int code
        (p (line (int->string (p))))
        (why (line (string-append "refused: " (extract why message))))
        (given eb)))))
;; A procedure taking one that does `e`: `e` taken, so its evidence exact.
(define taking
  (poly ((e effect))
    (subr (maxeff said e) ((effectrep e) datum (subr e () unit)) unit))
  (plambda ((e effect))
    (lambda (er code f)
      (stage api pure (subr e ((subr e () unit)) int) code
        (p (line (int->string ((p) f))))
        (why (line (string-append "refused: " (extract why message))))
        (given er)))))
;; A frozen list of at most `t`: `t` given there, so a bound may stand.
(define listing
  (poly ((t type)) (subr (maxeff said) ((typebound t) datum) unit))
  (plambda ((t type))
    (lambda (tb code)
      (stage api pure (listof t acyclic) code
        (p (line (int->string (length (p)))))
        (why (line (string-append "refused: " (extract why message))))
        (given tb)))))
(define main
  (subr (maxeff said (read (globals within taking listing line))) () int)
  (lambda ()
    (begin
      ((proj within (io stdout)) ((proj effect-bound pure) (reify-effect pure)) '(+ x 1))
      ((proj within (io stdout)) ((proj effect-bound pure) (reify-effect pure))
                                 '(begin (write-out "out\n") x))
      ((proj within (io stdout)) (effect-bound (reify-effect (io stdout)))
                                 '(begin (write-out "out\n") x))
      ((proj taking (io stdout)) (reify-effect (io stdout)) '(lambda (g) (begin (g) x))
                                 (lambda () (begin (write-out "called\n") #u)))
      ((proj listing int) ((proj type-bound int) (reify-type int)) '(list x x x))
      0)))
