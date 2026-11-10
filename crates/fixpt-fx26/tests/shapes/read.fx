;; Modules whose shapes are read from what binds them (`macros/shapes.rs`'s
;; test): a module, one of a declared type, a functor's result, a file's,
;; and a module a module gives.
(define-type sig (moduleof (val x int) (desc t int)))
(define m (module (define-type t int) (define x int 5) (define sub (module (define z int 1)))))
(define n sig m)
(define f (lambda () (module (define y int 3))))
(define g (f))
(define p ((proj (load-module "fx26:parser-types.fx") @s @e @m @c @p)))
(define main (lambda () (+ (+ (with m (the t x)) (with n x)) (+ (with g y) (with m (with sub z))))))
(define q (lambda () (with p e-var)))
