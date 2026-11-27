;; Over a.fx; its type names a.fx's.
(module-parameters ((m-a (load-moduleof "ifm-a.fx") #:qualified)))
(hide (import m-a mk (type t)))
(define-type u (productof (inner t) (tag string)))
(define wrap (subr pure (int) u) (lambda ((n int)) (product (inner (mk n)) (tag "b"))))
