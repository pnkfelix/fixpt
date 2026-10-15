;; => 45
;; `(import m name …)`: what module `m` gives, by name, defined here, as
;; `(define x (with m x))` would; types and effects marked, `(type t …)`,
;; `(effect e …)`. At the top level, in a module, and hidden there.
(define shapes
  (module
    (define-type point (productof (1 int) (2 int)))
    (define-effect touches (maxeff (read @heap) (write @heap)))
    (define origin point (product (1 0) (2 0)))
    (define bump (subr touches ((ref int @heap)) unit) (lambda (c) (set c (+ (get c) 1))))
    (define x-of (subr pure (point) int) (lambda (p) (extract p 1)))))
(import shapes origin bump (type point) (effect touches))
(define m
  (module
    (hide (import shapes x-of (type point)))
    (define far point (product (1 40) (2 2)))
    (define reach (subr pure (point) int) (lambda (p) (+ (x-of p) 3)))))
(define-type bumper (subr touches ((ref int @heap)) unit))
(define b bumper bump)
(let ((c (the (ref int @heap) (new 1))))
  (begin (b c) (+ (get c) (+ (extract origin 1) ((with m reach) (with m far))))))
