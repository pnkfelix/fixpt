;; => (x m x)
;; A true union of two sums is one sum, each tag once (logical-types.md
;; §8.5, U2): `(anyof expr op)` is a sub-sum of `sexp` as written, and an
;; `expr` and an `op` are each one.
(define-type expr (sumof (var symbol) (lam (productof (1 symbol) (2 expr)))
                         (app (productof (1 expr) (2 expr)))))
(define-type op (sumof (var symbol) (mac string)))
(define-type sexp (sumof (var symbol) (lam (productof (1 symbol) (2 expr)))
                         (app (productof (1 expr) (2 expr)))
                         (mac string) (pair (productof (1 sexp) (2 sexp))) (end unit)))
(define-type eop (anyof expr op))
(define* head (subr pure (sexp) symbol)
  (lambda (s) (tagcase s (var x x) (lam p (extract p 1)) (mac m 'm) (else y 'other))))
(define* via (subr pure (eop) symbol) (lambda (v) (head v)))
(define e1 expr (sum lam (product (1 'x) (2 (sum var 'y)))))
(define o1 op (sum mac "m"))
(define v1 (sumof (var symbol)) (sum var 'x))
(list (via e1) (via o1) (via v1))
