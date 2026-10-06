;; ! argument 1 is a int, where a exp is expected
;; A type a global module's type is re-exported as is shown by its name, as
;; is a type that holds it: `exp`, not the pair it is. Each `(select m syn)`
;; is the module's type itself once resolved, not a copy per use.
(define m (module (define-type syn (listof int acyclic)) (define one int 1)))
(define-type syn (select m syn))
(define-type exp (pairof syn int acyclic))
(define f (subr pure (exp) int) (lambda (e) (cdr e)))
(f 1)
