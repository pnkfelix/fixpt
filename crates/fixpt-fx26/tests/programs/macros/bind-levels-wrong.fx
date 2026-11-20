;; ! `body` is placed in the scope of `go`, and inside that of `(x ...)`, but its signature says it
;; Its levels the other way about, the loop's variables outside `go`: not what the template does.
(define-syntax loop
  (macro (_ go @ bvar desc cs @ ((x @ bvar desc expr) ...) desc body @ expr) expr
    (bind go in cs) (bind (x ...) go in body))
  (syntax-rules
    ((_ go eff ((x t i) ...) r body)
     (letrec ((go (subr eff (t ...) r) (lambda (x ...) body))) (go i ...)))))
(loop go spin ((i int 0)) int i)
