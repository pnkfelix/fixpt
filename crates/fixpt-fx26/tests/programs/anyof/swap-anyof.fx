;; => (y m)
;; Herman and Wand's swap of an expression or an operator, an `(anyof expr
;; op)`: taken apart by its members (logical-types.md §8.5, rule 5), each
;; keeps its sort, so the result is an `(anyof expr op)` again, as its
;; written members (a union of sums is kept as written, made one sum only
;; where one is needed: `tagcase`).
(define-type expr (sumof (var symbol) (lam (productof (1 symbol) (2 expr)))
                         (app (productof (1 expr) (2 expr)))))
(define-type op (sumof (var symbol) (mac string)))
(define-type sexp (sumof (var symbol) (lam (productof (1 symbol) (2 expr)))
                         (app (productof (1 expr) (2 expr)))
                         (mac string) (pair (productof (1 sexp) (2 sexp))) (end unit)))
(define-type swapper (allof (subr pure (symbol symbol expr) expr)
                            (subr pure (symbol symbol op) op)
                            (subr pure (symbol symbol sexp) sexp)))
;; Bound by a local `letrec`, its calls of itself read no global.
(define swap swapper
  (letrec ((name (subr pure (symbol symbol symbol) symbol)
             (lambda (a b x) (cond ((eq? x a) b) ((eq? x b) a) (else x))))
           (swap swapper
             (lambda (a b s)
               (tagcase s
                 (var x (sum var (name a b x)))
                 (lam p (sum lam (product (1 (name a b (extract p 1)))
                                          (2 (swap a b (extract p 2))))))
                 (app p (sum app (product (1 (swap a b (extract p 1)))
                                          (2 (swap a b (extract p 2))))))
                 (mac m (sum mac m))                         ; not an `expr`'s: skipped there
                 (pair p (sum pair (product (1 (swap a b (extract p 1)))
                                            (2 (swap a b (extract p 2))))))
                 (end u (sum end u))))))                     ; only an `sexp`'s
    swap))
;; Either sort swapped is either sort.
(define-type eop (anyof expr op))
(define* swap-eop (subr pure (eop) eop) (lambda (v) (swap 'x 'y v)))
(define* name-of (subr pure (eop) symbol)
  (lambda (v) (tagcase v (var x x) (mac m 'm) (else y 'none))))
(list (name-of (swap-eop (sum var 'x))) (name-of (swap-eop (sum mac "m"))))
