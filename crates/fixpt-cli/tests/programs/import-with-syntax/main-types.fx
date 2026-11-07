;; The file's `meters`, `int`, not the type variable the `plambda` binds.
(define units (load-module "units.fx"))
(import-with-syntax units)
(define g (poly ((meters type)) (subr pure (meters) int))
  (plambda ((meters type))
    (lambda ((x meters)) (+ (as-meters 5) ((as-fun (lambda ((y int)) y)) 7)))))
((proj g bool) #t)
