;; A module's file with a value and a type, re-exported by `reexports.fx`.
(define bump (subr pure (int) int) (lambda (x) (+ x 1)))
(define-type num int)
