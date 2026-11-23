;; => 5
;; A global is a path's base, one value until it is defined again; then
;; what used it runs again (`v`), so a value of the old one's path is not
;; kept: `v` is the new `both`'s `m1`'s `zero` ("seven"), its `value` 5.
(define-type sig (moduleof (abs t type) (val zero t) (val value (subr pure (t) int))))
(define make (subr pure (bool) sig)
  (lambda (b)
    (if b
        (module (define-generative t int #:seal up #:unseal down)
                (define zero t (up 7))
                (define value (subr pure (t) int) (lambda (c) (+ (down c) 1))))
        (module (define-generative t string #:seal up #:unseal down)
                (define zero t (up "seven"))
                (define value (subr pure (t) int) (lambda (c) (string-length (down c))))))))
(define both (module (define m1 (make #t)) (define m2 (make #f))))
(define v (with both (with m1 zero)))
(define both (module (define m1 (make #f)) (define m2 (make #t))))
((with both (with m1 value)) v)
