;; A session (`docs/research/eval.md`, "Sessions"): definitions that last
;; between pieces of code staged against a module, each checked (pending),
;; then committed as the program decides; redefinitions reported, refused,
;; or made; a host's name shadowed; a pending definition gone stale.
(define api (module (define base 10) (define twice (lambda ((n int)) (* 2 n)))))
(define-type api-type (moduleof (val base int) (val twice (subr pure (int) int))))
(define s (sessionof api-type @heap) (make-session api))
(define-effect sessioning
  (maxeff stage spin (read @heap) (write @heap) (read (globals s message defined joined))))
(define message (subr pure (stage-failure) string) (lambda (why) (extract why message)))
;; A definition, committed as `decision` says.
(define defined (subr sessioning (datum session-decision) string)
  (lambda (code decision)
    (session-define s pure code
      (d (tagcase (session-commit! s d decision)
           (defined u "defined")
           (failed why (string-append "not defined: " (message why)))))
      (why (string-append "refused: " (message why))))))
;; Code staged in the session, an `int`.
(define value (subr sessioning (datum) string)
  (lambda (code)
    (session-stage s spin int code
      (p (int->string (p)))
      (why (string-append "refused: " (message why))))))
(define joined (subr (maxeff spin (read (globals joined))) ((listof string acyclic)) string)
  (lambda (xs) (if (null? xs) "" (string-append " " (car xs) (joined (cdr xs))))))
;; What a definition would redefine.
(define redefinition (subr sessioning (datum) string)
  (lambda (code)
    (session-define s pure code
      (d (tagcase (session-redefines s d)
           (fresh u "fresh")
           (redefines r (string-append (extract r name) ": " (extract r old) " to " (extract r new)
                                       ", used by" (joined (extract r users))))))
      (why (string-append "refused: " (message why))))))
;; A definition checked, another committed, then the first: stale.
(define stale (subr sessioning () string)
  (lambda ()
    (session-define s pure '(define late 1)
      (d (begin (defined '(define early 2) (sum shadow #u))
                (tagcase (session-commit! s d (sum shadow #u))
                  (defined u "defined")
                  (failed why (string-append "not defined: " (message why))))))
      (why (string-append "refused: " (message why))))))
(define line (subr (io stdout) (string) unit)
  (lambda (x) (begin (write-out (string-append x "\n")) #u)))
(define main
  (subr (maxeff sessioning (io stdout)
                (read (globals defined value redefinition stale line message joined)))
        () int)
  (lambda ()
    (begin
      (line (defined '(define a (+ base 1)) (sum shadow #u)))
      (line (value '(+ a (twice a))))
      (line (defined '(define f (subr spin (int) int)
                         (lambda ((n int)) (if (= n 0) 1 (* n (f (- n 1))))))
                     (sum shadow #u)))
      (line (value '(f 5)))
      (line (defined '(define g (lambda ((n int)) (+ n a))) (sum shadow #u)))
      (line (redefinition '(define a "x")))
      (line (redefinition '(define b 1)))
      (line (defined '(define a 100) (sum refuse #u)))
      (line (value '(g 1)))
      (line (defined '(define a 100) (sum shadow #u)))
      (line (value '(g 1)))
      (line (defined '(define twice (lambda ((n int)) (* 3 n))) (sum shadow #u)))
      (line (value '(twice 1)))
      (line (stale))
      (line (value '(+ 1 "x")))
      (line (defined '(define h (car 1)) (sum shadow #u)))
      ;; Defined again at a type `g` cannot take, its users run again: `g`
      ;; no longer checks, and is broken.
      (line (defined '(define a "s") (sum rerun #u)))
      (line (value '(g 1)))
      0)))
