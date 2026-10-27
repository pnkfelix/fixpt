;; ! `(c …)` applies `c`, but `(select c t)` after it names `c`: to name a parameter, write `(c : type)`
;; A parameter is named `(c : sig)`; `(c sig)` is `c` applied.
(define-type sig (moduleof (abs t type) (val zero t)))
(define f (subr pure ((c sig) (select c t)) int) (lambda (c v) 1))
