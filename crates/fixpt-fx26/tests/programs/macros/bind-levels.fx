;; => 17
;; One `bind` of a part's levels, outermost first: the body in the scope of the loop's
;; procedure `go`, and inside that of its variables (Heist's should-work note, entry 2).
(define-syntax loop
  (macro (_ go @ bvar desc cs @ ((x @ bvar desc expr) ...) desc body @ expr) expr
    (bind go in cs) (bind go (x ...) in body))
  (syntax-rules
    ((_ go eff ((x t i) ...) r body)
     (letrec ((go (subr eff (t ...) r) (lambda (x ...) body))) (go i ...)))))
(define acc int 7)
(loop go spin ((i int 0) (acc int acc)) int (if (> i 4) acc (go (+ i 1) (+ acc i))))
