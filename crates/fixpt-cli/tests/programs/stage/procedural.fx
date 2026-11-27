;;; Procedural macros where staging runs, inside a call-out from the
;;; program's code, native code in the native convention (`TODO.md` §312):
;;; a staged load of a file that defines one, and a session's step that
;;; does, both expanded as a program's are.
(define m (module (define one int 1)))
(define staged
  (subr (maxeff stage spin (io stdout) (read @globals)) (datum)
        (sumof (#:done unit) (#:failed io-error)))
  (lambda (code)
    (stage m spin int code
      (p (write-out (string-append (int->string (p)) "\n")))
      (why (write-out (string-append "refused: " (extract why message) "\n"))))))
(staged '(let ((s (load-module "loads/swapping.fx"))) (with s ten)))
(define s (sessionof (moduleof (val one int)) @heap) (make-session m))
(define stepped
  (subr (maxeff stage spin (read @heap) (write @heap) (io stdout) (read (globals s))) (datum)
        (sumof (#:done unit) (#:failed io-error)))
  (lambda (code)
    (session-check s spin int code
      (c (tagcase c
           (expression p (write-out (string-append (int->string (p)) "\n")))
           (definition d
             (tagcase (session-commit! s d (sum shadow #u))
               (defined n (write-out (string-append "defined " n "\n")))
               (failed why
                 (write-out (string-append "not defined: " (extract why message) "\n")))))))
      (why (write-out (string-append "refused: " (extract why message) "\n"))))))
(stepped '(define-syntax flip
            (macro (_ f @ expr a @ expr b @ expr) expr)
            (er-macro-transformer
              (lambda (form rename compare)
                (list (car (cdr form)) (car (cdr (cdr (cdr form)))) (car (cdr (cdr form))))))))
(stepped '(flip - 2 12))
