;; ! `define*` `ev` is in a recursive group with `od`: use `define`
;; As at the top level, where a `define*` is in no `define-rec`.
(define m (module
  (define* ev (subr spin (int) bool) (lambda (n) (if (= n 0) #t (od (- n 1)))))
  (define od (subr spin (int) bool) (lambda (n) (if (= n 0) #f (ev (- n 1)))))))
1
