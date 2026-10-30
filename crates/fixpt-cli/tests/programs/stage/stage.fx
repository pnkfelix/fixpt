;; `stage` (`docs/research/eval.md`): code given as a datum, checked as the
;; program runs against a module's type, an effect and a type, and made a
;; procedure; or refused, why and where said as a value.
(define api
  (module (define x 41)
          (define bump (lambda ((n int)) (+ n 1)))
          (define say (lambda ((s string)) (begin (write-out s) #u)))))
(define failure (subr pure (stage-failure) string)
  (lambda (why)
    (string-append (tagcase (extract why kind)
                     (unread u "unread") (malformed u "malformed") (refused u "refused")
                     (stale u "stale"))
                   " " (int->string (extract why start)) " " (int->string (extract why end))
                   ": " (extract why message))))
(define number (subr (maxeff stage spin (read (globals api failure))) (datum) string)
  (lambda (code)
    (stage api pure int code
      (p (int->string (p)))
      (why (failure why)))))
;; Many, each made while values wait on the stack, so that collections
;; come as the checker runs.
(define-rec
  (many (subr (maxeff stage spin (read (globals api many))) (int string) string)
    (lambda (n acc)
      (if (= n 0)
          acc
          (stage api pure int '(bump x)
            (p (many (- n 1) (string-append acc (int->string (- (p) 41)))))
            (why (extract why message)))))))
(define line (subr (io stdout) (string) unit)
  (lambda (s) (begin (write-out (string-append s "\n")) #u)))
(define main
  (subr (maxeff stage spin (io stdout) (read (globals api number line failure many))) () int)
  (lambda ()
    (begin
      (line (number '(bump x)))
      (line (number '(let ((y 1)) (+ y (bump x)))))
      ;; A type the code does not have.
      (line (number '(bump "no")))
      ;; A name the module does not give.
      (line (number '(bump z)))
      ;; Writing, where the effect allowed is `pure`.
      (line (number '(begin (say "no") 1)))
      ;; Not an expression.
      (line (number '(define y 1)))
      ;; Within the effect allowed: the thunk writes when called.
      (stage api (io stdout) unit '(say "said\n")
        (p (begin (line "made") (p)))
        (why (line (failure why))))
      (line (many 30 ""))
      ;; A procedure made.
      (stage api pure (subr pure (int) int) '(lambda ((n int)) (* n (bump x)))
        (p (line (int->string ((p) 2))))
        (why (line (failure why))))
      0)))
