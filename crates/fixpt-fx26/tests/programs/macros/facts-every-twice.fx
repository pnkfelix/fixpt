;; => #t
;; `letrec` by ellipsis, its signature written: every repetition's binders, `(f ...)`, named by
;; two facts, each element exporting `f` once, as inferred.
(define-syntax my-letrec
  (macro (_ bs @ ((f @ bvar lambda) ...) body @ expr) expr
    (bind (f ...) in bs) (bind (f ...) in body))
  (syntax-rules
    ((_ ((f e) ...) body) (letrec ((f (subr spin (int) bool) e) ...) body))))
(my-letrec ((ev (lambda ((n int)) (if (= n 0) #t (od (- n 1)))))
            (od (lambda ((n int)) (if (= n 0) #f (ev (- n 1))))))
  (ev 10))
