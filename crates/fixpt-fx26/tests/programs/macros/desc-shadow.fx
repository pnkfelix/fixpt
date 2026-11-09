;; ! `a` is referred to where another of the pattern's binders may shadow it
;; Herman's K, of descriptions: a use giving both one name would change
;; what `a` refers to.
(define-syntax k2
  (dvar dvar)
  (syntax-rules ()
    ((_ a b) (plambda ((a type)) (plambda ((b type)) (lambda ((x a)) x))))))
1
