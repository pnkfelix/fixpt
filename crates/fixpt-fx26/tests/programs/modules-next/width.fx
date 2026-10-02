;; => 0
;; A module given where a type with fewer of its values is wanted: made
;; into a module of that type (`first-class-modules.md`, M4).
(define counter
  (module
    (define-generative t int)
    (define zero t (up-t 0))
    (define inc (subr pure (t) t) (lambda (c) (up-t (+ (down-t c) 1))))
    (define value (subr pure (t) int) (lambda (c) (down-t c)))))
(define-type zeros (moduleof (abs t type) (val zero t) (val value (subr pure (t) int))))
(define read-zero (subr pure (zeros) int) (lambda (m) (with m (value zero))))
(read-zero counter)
