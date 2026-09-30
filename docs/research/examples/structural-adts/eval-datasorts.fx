;;; FX-26 today: the typed evaluator as datasort refinements (Freeman and
;;; Pfenning), with no GADT machinery and nothing generative. One structural
;;; type per index value: `int-exp` and `bool-exp` are the expressions of
;;; each type, and `any-exp` all of them. Both refine `any-exp` by width
;;; subtyping and equi-recursion, and each evaluator returns its value with
;;; no tag to check; an ill-typed expression cannot be built at `int-exp`.
(define-type int-exp
  (sumof (int-e int)
         (add (productof (l int-exp) (r int-exp)))
         (if-e (productof (c bool-exp) (t int-exp) (f int-exp)))))
(define-type bool-exp
  (sumof (bool-e bool)
         (is-zero int-exp)
         (if-e (productof (c bool-exp) (t bool-exp) (f bool-exp)))))
(define-type any-exp
  (sumof (int-e int) (bool-e bool)
         (add (productof (l any-exp) (r any-exp)))
         (is-zero any-exp)
         (if-e (productof (c any-exp) (t any-exp) (f any-exp)))))
(define eval-int (subr pure (int-exp) int)
  (letrec ((eval-int (subr pure (int-exp) int)
             (lambda (e)
               (tagcase e
                 (int-e n n)
                 (add (l r) (+ (eval-int l) (eval-int r)))
                 (if-e (c t f) (if (eval-bool c) (eval-int t) (eval-int f))))))
           (eval-bool (subr pure (bool-exp) bool)
             (lambda (e)
               (tagcase e
                 (bool-e b b)
                 (is-zero x (= (eval-int x) 0))
                 (if-e (c t f) (if (eval-bool c) (eval-bool t) (eval-bool f)))))))
    eval-int))
(define one int-exp (sum int-e 1))
(define prog int-exp
  (sum if-e (product (c (sum is-zero (sum add (product (l one) (r (sum int-e -1))))))
                     (t (sum int-e 42))
                     (f one))))
(define untyped any-exp prog)   ; the same value, forgetting its type
(eval-int prog)
