;; => 9
;; Herman's `lambda`, through the kernel's: the macro's formals, typed
;; ones only, a rib, each in scope in the types after it; the body in its
;; scope. The template places them where the kernel's `lambda` takes
;; formals of more shapes (subtyping, binding structure alike).
(define-syntax fun
  ;; As named: ((fs (formals)) (body (in expr fs))), formals as
  ;; (union nil (exports ((x bvar) (t type) . (in (xs formals) x)) (rib x xs))).
  ((mu f (union (export () (rho))
                (export ((bvar type) . (import f (rho (AA var)))) (rho (AA var) (D rib)))))
   (import expr (rho (A rib))))
  (syntax-rules ()
    ((_ fs body) (lambda fs body))))
((fun ((a int) (b int)) (* a b)) 3 3)
