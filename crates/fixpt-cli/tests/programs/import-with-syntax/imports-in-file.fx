;; A module file importing another's macros: a program's alone, not yet
;; (`binding-shapes.md`, step 4; Heist's (b)).
(define lib (load-module "macros-only.fx"))
(import-with-syntax lib)
(define g (subr pure (int) int) (lambda (n) (twice n)))
