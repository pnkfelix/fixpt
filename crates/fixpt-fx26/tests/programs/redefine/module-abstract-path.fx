;; => 5
;; As `module-abstract.fx`, the abstract type a path's, `mid.a..t`.
(define make-int
  (lambda ()
    (module
      (define-generative t int #:seal up #:unseal down)
      (define zero t (up 0))
      (define value (subr pure (t) int) (lambda (c) (down c))))))
(define make-str
  (lambda ()
    (module
      (define-generative t string #:seal up #:unseal down)
      (define zero t (up "hello"))
      (define value (subr pure (t) int) (lambda (c) (string-length (down c)))))))
(define mid (module (define a (make-int))))
(define one (with (with mid a) zero))
(define use (lambda () ((with (with mid a) value) one)))
(define mid (module (define a (make-str))))
(use)
