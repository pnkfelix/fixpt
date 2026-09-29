;;; FX-26 today: phantom types (Leijen and Meijer, 1999). A generative type
;;; `(exp a)` wraps the untyped `expr`; its parameter is used nowhere in the
;;; representation, and is invariant, so it means only what the smart
;;; constructors below say. Building an ill-typed expression is refused
;;; (`eval-phantom-refused.fx`), but `eval` still checks tags at run time:
;;; nothing tells the checker that an `(exp int)` holds an `int-e` or an `add`.
(define-datatype expr
  (int-e int) (bool-e bool)
  (add expr expr) (if-e expr expr expr))
(define-generative (exp (a type)) expr)
(define* int-x (subr pure (int) (exp int)) (lambda (n) (up-exp (int-e n))))
(define* bool-x (subr pure (bool) (exp bool)) (lambda (b) (up-exp (bool-e b))))
(define* add-x (subr pure ((exp int) (exp int)) (exp int))
  (lambda (x y) (up-exp (add (down-exp x) (down-exp y)))))
(define* if-x (poly ((a type)) (subr pure ((exp bool) (exp a) (exp a)) (exp a)))
  (lambda (c t f) (up-exp (if-e (down-exp c) (down-exp t) (down-exp f)))))
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
;; The `else` can never run, but only we know that.
(define* run-int (subr spin ((exp int)) int)
  (lambda (e) (tagcase (eval (down-exp e)) (vint (n) n) (else v -1))))
(run-int (if-x (bool-x #t) (add-x (int-x 1) (int-x 2)) (int-x 0)))
