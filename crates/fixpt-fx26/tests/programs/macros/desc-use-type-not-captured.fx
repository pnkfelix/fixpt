;; => 5
;; A use's type `a`, the top level's, placed inside a template's `plambda`
;; that binds `a`: not captured, the template's made fresh.
(define-type a int)
(define-syntax wrap (type expr)
  (syntax-rules ()
    ((_ t e) ((proj (plambda ((a type)) (lambda ((x t)) x)) bool) e))))
(wrap a 5)
