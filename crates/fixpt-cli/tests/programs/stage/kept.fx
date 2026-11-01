;; Stages one after another, each checked by a front end that keeps the
;; standard environment between them (`check-staged`): what one binds,
;; refused or made, is not there for the next.
(define api
  (module (define x 41)
          (define bump (lambda ((n int)) (+ n 1)))))
(define failure (subr pure (stage-failure) string)
  (lambda (why) (string-append "refused: " (extract why message))))
(define number (subr (maxeff stage spin (read (globals api failure))) (datum) string)
  (lambda (code)
    (stage api pure int code
      (p (int->string (p)))
      (why (failure why)))))
(define line (subr (io stdout) (string) unit)
  (lambda (s) (begin (write-out (string-append s "\n")) #u)))
(define main
  (subr (maxeff stage spin (io stdout) (read (globals api number line failure))) () int)
  (lambda ()
    (begin
      ;; `y` bound, then the check refused.
      (line (number '(let ((y 1)) (+ y "a"))))
      (line (number 'y))
      ;; Made, and its `y` gone after.
      (line (number '(let ((y 2)) (bump y))))
      (line (number 'y))
      ;; The wrapping's parameter, the module itself, as every stage sees it.
      (line (number 'stage-module))
      (line (number '(bump x)))
      0)))
