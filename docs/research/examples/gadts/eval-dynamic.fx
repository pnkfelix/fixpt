;;; FX-26 today: the classic GADT evaluator without GADTs. Expressions are
;;; untyped; values carry a tag, and every use checks it at run time. An
;;; ill-typed expression is accepted, and evaluates to `wrong`.
(define-datatype expr
  (int-e int) (bool-e bool)
  (add expr expr) (if-e expr expr expr))
(define-datatype val (vint int) (vbool bool) (wrong unit))
(define* eval (subr spin (expr) val)
  (lambda (e)
    (tagcase e
      (int-e (n) (vint n))
      (bool-e (b) (vbool b))
      (add (x y) (tagcase (eval x)
                   (vint (m) (tagcase (eval y) (vint (n) (vint (+ m n))) (else v (wrong #u))))
                   (else v (wrong #u))))
      (if-e (c t f) (tagcase (eval c)
                      (vbool (b) (if b (eval t) (eval f)))
                      (else v (wrong #u)))))))
(define* as-int (subr pure (val) int) (lambda (v) (tagcase v (vint (n) n) (else w -1))))
(+ (as-int (eval (if-e (bool-e #t) (add (int-e 1) (int-e 2)) (int-e 0))))   ; 3
   (* 100 (as-int (eval (add (int-e 1) (bool-e #f))))))                     ; wrong: -1
