;; => 2
;; An `include`'s types are in scope in the module's items (`TODO.md` §69):
;; `point` is `shapes`'s, in a value's type and in a `define-type`.
(define shapes (module (define-type point (productof (1 int) (2 int)))
                       (define origin (productof (1 int) (2 int)) (product (1 0) (2 0)))))
(define m
  (module
    (include shapes)
    (define flip (subr pure (point) point)
      (lambda (p) (product (1 (extract p 2)) (2 (extract p 1)))))
    (define-type pair point)
    (define one pair (product (1 1) (2 2)))))
(extract ((with m flip) (with m one)) 1)
