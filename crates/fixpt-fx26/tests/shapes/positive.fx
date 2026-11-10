;; Shapes in a function's positive places (`macros/shapes.rs`'s test): a
;; callback's parameter, given the module a procedure's type says it gives
;; it; and a module that gives a functor.
(define-type sig (moduleof (val x int)))
(define m (module (define x int 5) (define mk (lambda () (module (define y int 1))))))
(define call (subr pure ((subr pure (sig) int) sig) int) (lambda (f s) (f s)))
(define main (lambda () (+ (call (lambda (n) (with n x)) m) (with m x))))
