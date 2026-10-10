;; => 7
;; A hidden `include`'s types are in scope too, and what a type shown
;; says of one is what it abbreviates: `norm` takes a `(productof …)`.
(define shapes (module (define-type point (productof (1 int) (2 int)))
                       (define origin (productof (1 int) (2 int)) (product (1 0) (2 0)))))
(define m
  (module
    (hide (include shapes))
    (define-effect touches (read @globals))
    (define norm (subr pure (point) int) (lambda (p) (+ (extract p 1) (extract p 2))))
    (define at-origin int (norm origin))))
(+ (with m at-origin) ((with m norm) (product (1 3) (2 4))))
