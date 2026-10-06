;; => 1
;; A parametric `define-datatype` in a module: a family, its constructors
;; polymorphic.
(define trees (module
  (define-datatype (tree (t type)) (leaf) (node t))
  (define size (poly ((t type)) (subr pure ((tree t)) int))
    (plambda ((t type)) (lambda (x) (tagcase x (leaf () 0) (node (v) 1)))))))
(define-type (tree (t type)) ((select trees tree) t))
((proj (with trees size) int) ((proj (with trees node) int) 7))
