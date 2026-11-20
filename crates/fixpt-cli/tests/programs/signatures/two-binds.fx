;; Two facts binding into one part: read as before, the later's level outside the earlier's,
;; and warned of (to be refused).
(define-syntax loop
  (macro (_ go @ bvar desc cs @ ((x @ bvar desc expr) ...) desc body @ expr) expr
    (bind go in cs) (bind (x ...) in body) (bind go in body))
  (syntax-rules
    ((_ go eff ((x t i) ...) r body)
     (letrec ((go (subr eff (t ...) r) (lambda (x ...) body))) (go i ...)))))
(loop go spin ((i int 0)) int (if (> i 4) i (go (+ i 1))))
