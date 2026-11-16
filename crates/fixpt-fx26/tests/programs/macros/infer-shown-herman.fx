;; ! inferred: (macro/addressed (bvar expr bvar (import expr (cage (rho ((path #:a) var)) (rho
;; A refused signature inferred that shapes and facts do not say, an import of two rings, shown
;; in Herman's form.
(define-syntax define-both
  (syntax-rules
    ((_ a e b e2 body)
     (begin (define a e) (define b (let ((a 1)) e2)) (define c (list body (let ((a 1)) body)))))))
(define-both x 1 y 2 3)
