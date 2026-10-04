;; ! a recursive type must be built from a constructor
;; Recursion only through a type function's application is no type once
;; the function is the identity: refused (recursion at the base kind only).
(define-type (fix (f (=> (type) type))) (f (fix f)))
(define g (poly ((f (=> (type) type))) (subr pure ((fix f)) int))
  (plambda ((f (=> (type) type))) (lambda (x) 1)))
