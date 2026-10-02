;;; FX-26 today: a typed evaluator with no tags at all. An `(exp a)` is its
;;; own meaning, a thunk giving an `a`, so `eval` is a call and cannot go
;;; wrong (the "finally tagless" style of Carette, Kiselyov and Shan 2009).
;;; The price: an expression can only be evaluated by *this one* interpreter;
;;; a second interpretation (print it, optimize it, count its nodes) needs a
;;; second family of `int-x`/`bool-x`/`add-x`/`if-x`, because abstracting over
;;; "which interpreter" needs a kind `type -> type` FX-26 does not have
;;; (identical to `crates/fixpt-fx26/tests/programs/gadts`'s sibling,
;;; `docs/research/examples/gadts/eval-closures.fx`; kept here too since this
;;; is the primary example `docs/research/higher-kinds.md` cites as a lighter
;;; interim that needs no new kind).
(define-type (exp (a type)) (subr pure () a))
(define int-x (subr pure (int) (exp int)) (lambda (n) (lambda () n)))
(define bool-x (subr pure (bool) (exp bool)) (lambda (b) (lambda () b)))
(define add-x (subr pure ((exp int) (exp int)) (exp int))
  (lambda (x y) (lambda () (+ (x) (y)))))
(define if-x (poly ((a type)) (subr pure ((exp bool) (exp a) (exp a)) (exp a)))
  (lambda (c t f) (lambda () (if (c) (t) (f)))))
(define eval (poly ((a type)) (subr pure ((exp a)) a)) (lambda (e) (e)))
(eval (if-x (bool-x #t) (add-x (int-x 1) (int-x 2)) (int-x 0)))
