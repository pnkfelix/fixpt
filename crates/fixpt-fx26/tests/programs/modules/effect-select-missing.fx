;; ! `(select m t)`: `m` has no effect `t`
(define m (module (define-type t int) (define x int 1)))
(define f (subr (select m t) () int) (lambda () 1))
1
