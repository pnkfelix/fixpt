;; => 1
;; Today's parametric kind system: a single kind-`type` binder
;; (`docs/fx26.md` "Generative types", ~line 1033). `bag` is invariant
;; in its element type `a` (a mutable heap pair can't be covariant);
;; `up-bag`/`down-bag` are generated automatically and are the identity
;; at run time. This is the baseline the higher-kinds note contrasts
;; with: `a` ranges over types, never over type CONSTRUCTORS, because
;; `(a type)` is the only shape a binder's kind can take for a type
;; parameter (kinds are flat: region, place, effect, type, data, size,
;; conv — `crates/fixpt-fx26/src/ast.rs` `enum Kind`, line 17).
(define-generative (bag (a type)) (listof a @heap))

(define make-bag
  (poly ((a type)) (subr (read (globals up-bag)) ((listof a @heap)) (bag a)))
  (plambda ((a type)) (lambda (xs) (up-bag xs))))

(define bag-first
  (poly ((a type)) (subr (maxeff (read (globals down-bag)) (read @heap)) ((bag a)) a))
  (plambda ((a type)) (lambda (b) (car (down-bag b)))))

(bag-first (make-bag (the (listof int @heap) (cons 1 (cons 2 nil)))))
