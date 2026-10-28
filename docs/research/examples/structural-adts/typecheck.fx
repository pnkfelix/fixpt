;;; FX-26 today: from untyped to typed expressions, structurally. The checker
;;; returns the expression at its refined type, as a sum saying which; the
;;; typed expressions are a subtype of the untyped ones, so nothing is
;;; converted to go back. (It rebuilds each node: a `tagcase` arm does not
;;; yet narrow the variable it tests, only bind the payload.)
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
(define-type typed (oneof (i int-exp) (b bool-exp) (wrong unit)))
(define typecheck (subr pure (any-exp) typed)
  (letrec ((tc (subr pure (any-exp) typed)
             (lambda (e)
               (tagcase e
                 (int-e n (one i (one int-e n)))
                 (bool-e v (one b (one bool-e v)))
                 (add (l r)
                   (tagcase (tc l)
                     (i x (tagcase (tc r)
                            (i y (one i (one add (tup (l x) (r y)))))
                            (else o (one wrong #u))))
                     (else o (one wrong #u))))
                 (is-zero x
                   (tagcase (tc x) (i y (one b (one is-zero y))) (else o (one wrong #u))))
                 (if-e (c t f)
                   (tagcase (tc c)
                     (b c2
                       (tagcase (tc t)
                         (i t2 (tagcase (tc f)
                                 (i f2 (one i (one if-e (tup (c c2) (t t2) (f f2)))))
                                 (else o (one wrong #u))))
                         (b t2 (tagcase (tc f)
                                 (b f2 (one b (one if-e (tup (c c2) (t t2) (f f2)))))
                                 (else o (one wrong #u))))
                         (wrong u (one wrong #u))))
                     (else o (one wrong #u))))))))
    tc))
(define-type answer (oneof (int-answer int) (bool-answer bool) (ill-typed unit)))
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
  (one if-e (tup (c (one bool-e #t)) (t (one int-e 2)) (f (one int-e 0)))))
(define input any-exp (one add (tup (l (one int-e 40)) (r choice))))
(tagcase (typecheck input)
  (i e (eval-int e))
  (else o -1))
