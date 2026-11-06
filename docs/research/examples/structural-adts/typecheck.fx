;;; FX-26 today: from untyped to typed expressions, structurally. The checker
;;; returns the expression at its refined type, as a sum saying which; the
;;; typed expressions are a subtype of the untyped ones, so nothing is
;;; converted to go back. (It rebuilds each node: a `tagcase` arm does not
;;; yet narrow the variable it tests, only bind the payload.)
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
(define-type typed (sumof (i int-exp) (b bool-exp) (wrong unit)))
(define typecheck (subr pure (any-exp) typed)
  (letrec ((tc (subr pure (any-exp) typed)
             (lambda (e)
               (tagcase e
                 (int-e n (sum i (sum int-e n)))
                 (bool-e v (sum b (sum bool-e v)))
                 (add (l r)
                   (tagcase (tc l)
                     (i x (tagcase (tc r)
                            (i y (sum i (sum add (tuple x y))))
                            (else o (sum wrong #u))))
                     (else o (sum wrong #u))))
                 (is-zero x
                   (tagcase (tc x) (i y (sum b (sum is-zero y))) (else o (sum wrong #u))))
                 (if-e (c t f)
                   (tagcase (tc c)
                     (b c2
                       (tagcase (tc t)
                         (i t2 (tagcase (tc f)
                                 (i f2 (sum i (sum if-e (tuple c2 t2 f2))))
                                 (else o (sum wrong #u))))
                         (b t2 (tagcase (tc f)
                                 (b f2 (sum b (sum if-e (tuple c2 t2 f2))))
                                 (else o (sum wrong #u))))
                         (wrong u (sum wrong #u))))
                     (else o (sum wrong #u))))))))
    tc))
(define-type answer (sumof (int-answer int) (bool-answer bool) (ill-typed unit)))
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
(define choice any-exp
  (sum if-e (tuple (sum bool-e #t) (sum int-e 2) (sum int-e 0))))
(define input any-exp (sum add (tuple (sum int-e 40) choice)))
(tagcase (typecheck input)
  (i e (eval-int e))
  (else o -1))
