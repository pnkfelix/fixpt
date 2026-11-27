;;; Staged code that loads files: each a module made afresh from the
;;; file's text as staging reads it (`docs/research/eval.md`, "Decided
;;; (the user's, 2026-11-26)"), its loads one module a path within it, as a
;;; program's are, and its generative types its own, not the program's.
(define base (load-module "loads/base.fx"))
(define m (module (define one int 1)))
(define say
  (subr (maxeff stage spin (io stdout) (read @globals)) (datum)
        (sumof (#:done unit) (#:failed io-error)))
  (lambda (code)
    (stage m (io stdout) int code
      (p (write-out (string-append (int->string (p)) "\n")))
      (why (write-out (string-append "refused: " (extract why message) "\n"))))))
;; A file, and what it loads.
(say '(let ((lib (load-module "loads/lib.fx"))) (with lib (double 21))))
(say '(let ((lib (load-module "loads/lib.fx")))
         ((with lib doubled-id) ((with lib base::make-id) 5))))
;; Two loads of a path in the code, one module.
(say '(let ((a (load-module "loads/base.fx")) (b (load-module "loads/base.fx")))
         ((with a id-number) ((with b make-id) 7))))
;; A file that is not there.
(say '(let ((m (load-module "loads/missing.fx"))) 1))
;; From another directory, as the program says (`stage-directory!`), a
;; relative one from where it was.
(stage-directory! "loads")
(say '(let ((b (load-module "base.fx"))) ((with b id-number) ((with b make-id) 3))))
