;; `again`'s code is at its use, line 11, not at the call beside it on line 10
;; (`TODO.md` §250: placed by its position in a text written out, it was).
(define-syntax again (expr expr expr) (syntax-rules () ((_ f n k)
  (f (- n 1) (- k 1)))))
(define* spin (subr spin (int int) int)
  (lambda (n k)
    (if (< k 1)
        n
        (if (< n 1)
            (spin (+ n 1) (- k 1))
            (again spin n k)))))
(spin 0 10)
