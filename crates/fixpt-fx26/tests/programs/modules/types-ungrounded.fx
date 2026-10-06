;; ! a recursive type must be built from a constructor, not only from names
(define m (module
  (define-type a b)
  (define-type b a)))
1
