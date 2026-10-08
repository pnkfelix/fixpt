;; A module's file that loads another and re-exports from it: `(define x
;; (with m x))`, the `x` there `m`'s, and a type its lambdas' types select.
(define m (load-module "bump.fx"))
(define bump (with m bump))
(define-type num (select m num))
(define twice (subr pure (num) num) (lambda (x) (bump (bump x))))
