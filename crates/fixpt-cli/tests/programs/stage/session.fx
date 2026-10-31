;; A session (`docs/research/eval.md`, "Sessions"): forms checked in it, an
;; expression's procedure called, a definition pending, then committed as
;; the program decides; redefinitions reported, refused, or made; a host's
;; name shadowed; a pending definition gone stale.
(define api (module (define base 10) (define twice (lambda ((n int)) (* 2 n)))))
(define-type api-type (moduleof (val base int) (val twice (subr pure (int) int))))
(define s (sessionof api-type @heap) (make-session api))
(define-effect sessioning
  (maxeff stage spin (read @heap) (write @heap) (read (globals s message form joined))))
(define message (subr pure (stage-failure) string) (lambda (why) (extract why message)))
;; A form checked in the session: an expression, evaluated at once, an
;; `int`; or a definition, committed as `decision` says.
(define form (subr sessioning (datum session-decision) string)
  (lambda (code decision)
    (session-check s spin int code
      (c (tagcase c
           (expression p (int->string (p)))
           (definition d
             (tagcase (session-commit! s d decision)
               (defined n (string-append "defined " n))
               (failed why (string-append "not defined: " (message why)))))))
      (why (string-append "refused: " (message why))))))
(define joined (subr (maxeff spin (read (globals joined))) ((listof string acyclic)) string)
  (lambda (xs) (if (null? xs) "" (string-append " " (car xs) (joined (cdr xs))))))
;; What a definition would redefine.
(define redefinition (subr sessioning (datum) string)
  (lambda (code)
    (session-check s spin int code
      (c (tagcase c
           (expression p "an expression")
           (definition d
             (tagcase (session-redefines s d)
               (fresh u "fresh")
               (redefines r (string-append (extract r name) ": " (extract r old) " to "
                                           (extract r new) ", used by"
                                           (joined (extract r users))))))))
      (why (string-append "refused: " (message why))))))
;; A definition checked, another committed, then the first: stale.
(define stale (subr sessioning () string)
  (lambda ()
    (session-check s pure unit '(define late 1)
      (c (tagcase c
           (expression p "an expression")
           (definition d
             (begin (form '(define early 2) (sum shadow #u))
                    (tagcase (session-commit! s d (sum shadow #u))
                      (defined n "defined")
                      (failed why (string-append "not defined: " (message why))))))))
      (why (string-append "refused: " (message why))))))
(define line (subr (io stdout) (string) unit)
  (lambda (x) (begin (write-out (string-append x "\n")) #u)))
(define main
  (subr (maxeff sessioning (io stdout)
                (read (globals form redefinition stale line message joined)))
        () int)
  (lambda ()
    (begin
      (line (form '(define a (+ base 1)) (sum shadow #u)))
      (line (form '(+ a (twice a)) (sum shadow #u)))
      (line (form '(define f (subr spin (int) int)
                         (lambda ((n int)) (if (= n 0) 1 (* n (f (- n 1))))))
                     (sum shadow #u)))
      (line (form '(f 5) (sum shadow #u)))
      (line (form '(define g (lambda ((n int)) (+ n a))) (sum shadow #u)))
      (line (redefinition '(define a "x")))
      (line (redefinition '(define b 1)))
      (line (form '(define a 100) (sum refuse #u)))
      (line (form '(g 1) (sum shadow #u)))
      (line (form '(define a 100) (sum shadow #u)))
      (line (form '(g 1) (sum shadow #u)))
      (line (form '(define twice (lambda ((n int)) (* 3 n))) (sum shadow #u)))
      (line (form '(twice 1) (sum shadow #u)))
      (line (stale))
      (line (form '(+ 1 "x") (sum shadow #u)))
      (line (form '(define h (car 1)) (sum shadow #u)))
      ;; Defined again at a type `g` cannot take, its users run again: `g`
      ;; no longer checks, and is broken.
      (line (form '(define a "s") (sum rerun #u)))
      (line (form '(g 1) (sum shadow #u)))
      0)))
