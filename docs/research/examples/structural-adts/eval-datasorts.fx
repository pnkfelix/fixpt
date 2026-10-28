;;; FX-26 today: the typed evaluator as datasort refinements (Freeman and
;;; Pfenning), with no GADT machinery and nothing generative. One structural
;;; type per index value: `int-exp` and `bool-exp` are the expressions of
;;; each type, and `any-exp` all of them. Both refine `any-exp` by width
;;; subtyping and equi-recursion, and each evaluator returns its value with
;;; no tag to check; an ill-typed expression cannot be built at `int-exp`.
(define-type int-exp
  (oneof (int-e int)
         (add (tupof (l int-exp) (r int-exp)))
         (if-e (tupof (c bool-exp) (t int-exp) (f int-exp)))))
(define-type bool-exp
  (oneof (bool-e bool)
         (is-zero int-exp)
         (if-e (tupof (c bool-exp) (t bool-exp) (f bool-exp)))))
(define-type any-exp
  (oneof (int-e int) (bool-e bool)
         (add (tupof (l any-exp) (r any-exp)))
         (is-zero any-exp)
         (if-e (tupof (c any-exp) (t any-exp) (f any-exp)))))
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
(define one int-exp (one int-e 1))
(define prog int-exp
  (one if-e (tup (c (one is-zero (one add (tup (l one) (r (one int-e -1))))))
                     (t (one int-e 42))
                     (f one))))
(define untyped any-exp prog)   ; the same value, forgetting its type
(eval-int prog)
