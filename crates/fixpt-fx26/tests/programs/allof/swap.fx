;; => (y x)
;; Herman and Wand's swap (ESOP 2008, §3), over λm's sorts written as
;; sub-sums of one another (the user's encoding): one body, a type for each
;; sort, each keeping its sort (`docs/research/logical-types.md` §8.5). An
;; `sexp`'s sequence is a chain of `pair`s ending in `end`.
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
;; An `expr` swapped is an `expr`: where one is expected, it is taken.
(define* body (subr pure (expr) expr)
  (lambda (e) (tagcase e (lam p (extract p 2)) (else y e))))
(define* name-of (subr pure (expr) symbol)
  (lambda (e) (tagcase e (var x x) (else y 'none))))
(define e1 expr
  (sum lam (product (1 'x) (2 (sum app (product (1 (sum var 'x)) (2 (sum var 'y))))))))
;; (lambda (x) (x y)), with `x` and `y` swapped: (lambda (y) (y x)); its body's names.
(tagcase (body (swap 'x 'y e1))
  (app p (list (name-of (extract p 1)) (name-of (extract p 2))))
  (else y nil))
