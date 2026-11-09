;; => #t
;; `letrec` by ellipsis: each lambda in every binder's scope, its signature
;; inferred, an import on the list of what the list exports.
(define-syntax my-letrec
  (syntax-rules ()
    ((_ ((f e) ...) body) (letrec ((f (subr spin (int) bool) e) ...) body))))
(my-letrec ((ev (lambda ((n int)) (if (= n 0) #t (od (- n 1)))))
            (od (lambda ((n int)) (if (= n 0) #f (ev (- n 1))))))
  (ev 10))
