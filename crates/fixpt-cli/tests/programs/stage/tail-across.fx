;; Staged code and the program's call each other in tail position (Heist's
;; request, `TODO.md` §201): a staged loop of a million steps that recurs
;; through a procedure of the program, `apply1`, runs in constant space.
(define api
  (module (define apply1 (subr spin ((subr spin (int) int) int) int) (lambda (f n) (f n)))))
(define main
  (subr (maxeff stage spin (io stdout) (read (globals api))) () int)
  (lambda ()
    (stage api spin int
      '(letrec ((go (subr spin (int) int)
                  (lambda (n) (if (<= n 0) 42 (apply1 go (- n 1))))))
         (go 1000000))
      (p (begin (write-out (string-append (int->string (p)) "\n")) 0))
      (why (begin (write-out (string-append "refused: " (extract why message) "\n")) 1)))))
