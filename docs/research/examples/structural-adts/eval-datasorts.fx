;;; FX-26 today: the typed evaluator as datasort refinements (Freeman and
;;; Pfenning), with no GADT machinery and nothing generative. One structural
;;; type per index value: `int-exp` and `bool-exp` are the expressions of
;;; each type, and `any-exp` all of them. Both refine `any-exp` by width
;;; subtyping and equi-recursion, and each evaluator returns its value with
;;; no tag to check; an ill-typed expression cannot be built at `int-exp`.
(define-type int-exp
  (sumof (int-e int)
         (add (tupleof int-exp int-exp))
         (if-e (tupleof bool-exp int-exp int-exp))))
(define-type bool-exp
  (sumof (bool-e bool)
         (is-zero int-exp)
         (if-e (tupleof bool-exp bool-exp bool-exp))))
(define-type any-exp
  (sumof (int-e int) (bool-e bool)
         (add (tupleof any-exp any-exp))
         (is-zero any-exp)
         (if-e (tupleof any-exp any-exp any-exp))))
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
  (sum if-e (tuple (sum is-zero (sum add (tuple one (sum int-e -1)))) (sum int-e 42) one)))
(define untyped any-exp prog)   ; the same value, forgetting its type
(eval-int prog)
