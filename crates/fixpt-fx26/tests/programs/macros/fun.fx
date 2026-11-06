;; => 9
;; Herman's `lambda`, through the kernel's: the macro's formals, typed
;; ones only, a rib; the body in its scope. The template places them where
;; the kernel's `lambda` takes formals of more shapes (subtyping, binding
;; structure alike).
(define-syntax fun
  ;; As named: ((fs (formals)) (body (in expr fs))), formals as
  ;; (union nil (exports ((x bvar) (t type) . (xs formals)) (rib x xs))).
  ((mu f (union (export () (rho))
                (export ((bvar type) . f) (rho (AA var) (D rib)))))
   (import expr (rho (A rib))))
  ((_ fs body) (lambda fs body)))
((fun ((a int) (b int)) (* a b)) 3 3)
