;; ! (macro (_ p1 @ ((f @ bvar lambda) ...) body @ (many expr)) expr (bind (f ...) in p1)
;; A refused signature inferred, shown in shapes and facts: what a list's elements bind, every
;; repetition's, `(f ...)`, named by two facts; the list labelled `p1`, its pattern no name.
(define-syntax m
  (syntax-rules
    ((_ ((f e) ...) body) (list (letrec ((f (subr spin (int) bool) e) ...) body) body))))
(m ((ev (lambda ((n int)) #t))) 3)
