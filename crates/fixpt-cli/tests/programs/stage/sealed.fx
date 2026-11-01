;; A stage against a module a global seals (Heist's request, `TODO.md`
;; §201): its abstract type `t`, opened as the global's (`rt..t`), printed
;; within the module type by its label, as its binder says, so that the
;; staged checker reads it back.
(define rt
  (the (moduleof (abs t type) (val zero t) (val succ (subr pure (t) t))
                 (val show (subr pure (t) int)))
       (module (define-type t int) (define zero t 0)
               (define succ (subr pure (t) t) (lambda (x) (+ x 1)))
               (define show (subr pure (t) int) (lambda (x) x)))))
(define main
  (subr (maxeff stage spin (io stdout) (read (globals rt))) () int)
  (lambda ()
    (stage rt pure int '(show (succ (succ zero)))
      (p (begin (write-out (string-append (int->string (p)) "\n")) 0))
      (why (begin (write-out (string-append "refused: " (extract why message) "\n")) 1)))))
