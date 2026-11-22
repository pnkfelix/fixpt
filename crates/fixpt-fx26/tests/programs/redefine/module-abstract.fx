;; => 5
;; A global whose module has abstract types names them for its binding,
;; `a..t`: a module defined there again, however like the old its type is
;; written, has others, so it is a new global, and `one` and `use` are
;; checked and defined again over it. Assigned, `use` would give the new
;; `value` the old `zero`, an `int` read as a `string`.
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
(define a (make-int))
(define one (with a zero))
(define use (lambda () ((with a value) one)))
(define a (make-str))
(use)
