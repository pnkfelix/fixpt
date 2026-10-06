;; => 1
;; Two of a module's types naming each other.
(define m (module
  (define-type a (sumof (stop (productof)) (more (productof (1 b)))))
  (define-type b (sumof (end (productof)) (again (productof (1 a)))))
  (define x a (sum stop (product)))))
1
