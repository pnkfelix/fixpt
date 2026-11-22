;; ! argument 1 is a mid0.a..t, where a outer.m.a..t is expected
;; A path's types are its base's binding's, and only that binding's: `m`,
;; a module's value opened by `with`, has the type `mid0` was bound at,
;; maybe, but may be `other0`, so its paths' types are their own.
(define make
  (lambda ()
    (module
      (define-generative t int #:seal up #:unseal down)
      (define zero t (up 0))
      (define value (subr pure (t) int) (lambda (c) (down c))))))
(define mid0 (module (define a (make))))
(define other0 (module (define a (make))))
(define outer (module (define m (if #t other0 mid0))))
(with outer ((with (with m a) value) (with (with mid0 a) zero)))
