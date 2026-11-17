;; => (2 2 3)
;; `with` and `select` of a path to a module, `(with m x)`: each the same
;; module wherever the path is read, so its abstract types are one,
;; `mid.a..t`, through a `let` or `define` of it too.
(define make
  (lambda ()
    (module
      (define-generative t int #:seal up #:unseal down)
      (define zero t (up 0))
      (define inc (subr pure (t) t) (lambda (c) (up (+ (down c) 1))))
      (define value (subr pure (t) int) (lambda (c) (down c))))))
(define mid (module (define a (make)) (define b 2)))
(define one (with (with mid a) (inc zero)))
(define p (with mid a))
(define bump (lambda ((x (select (with mid a) t))) ((with p inc) x)))
(list ((with (with mid a) value) (bump one))
      (let ((q (with mid a))) ((with q value) ((with q inc) one)))
      (with (with mid a) (value (the t (bump (bump one))))))
