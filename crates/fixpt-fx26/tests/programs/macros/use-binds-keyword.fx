;; => 10
;; A use binding a name that is a keyword (`fields`, a bloblet's), as the
;; `letrec` it stands for may (Heist's): a template's forms are read by
;; their heads, which no binding of the use's names.
(define-syntax loop
  (syntax-rules ()
    ((_ go eff ((x t i) ...) r body)
     (letrec ((go (subr eff (t ...) r) (lambda (x ...) body))) (go i ...)))))
(define looped (subr spin (int) int)
  (lambda (n) (loop fields spin ((i int n) (a int 0)) int (if (= i 0) a (fields (- i 1) (+ a i))))))
(looped 4)
