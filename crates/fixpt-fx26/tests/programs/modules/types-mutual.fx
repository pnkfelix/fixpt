;; => 1
;; Two of a module's types naming each other.
(define m (module
  (define-type a (oneof (stop (tupof)) (more (tupof (1 b)))))
  (define-type b (oneof (end (tupof)) (again (tupof (1 a)))))
  (define x a (one stop (tup)))))
1
