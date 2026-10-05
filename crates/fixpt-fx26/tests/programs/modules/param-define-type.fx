;; => 3
;; A parameterised `define-type` in a module is a description function:
;; `(define-type (pair2 (a type)) T)` is `(define-type pair2 (dlambda ((a
;; type)) T))`.
(define m (module (define-type (pair2 (a type)) (productof (1 a) (2 a)))
                  (define x (pair2 int) (product (1 1) (2 2)))))
(with m (+ (extract x 1) (extract x 2)))
