;; => 9
;; Herman's `lambda`, through the kernel's: the macro's formals, typed
;; ones only, a rib, each in scope in the types after it; the body in its
;; scope. The template places them where the kernel's `lambda` takes
;; formals of more shapes (subtyping, binding structure alike).
(define-syntax fun
  (macro (letrec-shape ((formals (union (none ())
                                      (formal ((x @ bvar t @ desc) rest @ . formals)
                                        (bind x in rest)
                                        (export x rest)))))
           (_ fs @ formals body @ expr))
         expr
    (bind fs in body))
  (syntax-rules
    ((_ fs body) (lambda fs body))))
((fun ((a int) (b int)) (* a b)) 3 3)
