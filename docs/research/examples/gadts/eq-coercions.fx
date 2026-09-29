;;; FX-26 today: a type-equality "witness" as a pair of coercions, one each
;;; way. `refl` builds the honest one, and `cast` uses it. Unlike the GADT
;;; `Refl`, nothing stops anyone building an `(eq int bool)` from two
;;; functions of their own, so holding one proves nothing to the checker,
;;; and a `tagcase` cannot learn `a = b` from it. (Leibniz equality,
;;; forall f. f a -> f b, would need a kind `type -> type`, which FX-26
;;; does not have.)
(define-type (eq (a type) (b type)) (productof (to (subr pure (a) b)) (from (subr pure (b) a))))
(define refl (poly ((a type)) (eq a a))
  (plambda ((a type)) (product (to (lambda ((x a)) x)) (from (lambda ((x a)) x)))))
(define cast (poly ((a type) (b type)) (subr pure ((eq a b) a) b))
  (lambda (w x) ((extract w to) x)))
(define sym (poly ((a type) (b type)) (subr pure ((eq a b)) (eq b a)))
  (lambda (w) (product (to (extract w from)) (from (extract w to)))))
(+ (cast (proj refl int) 41) (cast (sym (proj refl int)) 1))
