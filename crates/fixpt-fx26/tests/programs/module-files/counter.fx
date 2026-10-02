;; A module's items, for `load-module` (`first-class-modules.md`, M7): a
;; counter whose type is abstract. Read alone, a program like any other.
(define-generative t int)
(define zero t (up-t 0))
(define inc (subr pure (t) t) (lambda (c) (up-t (+ (down-t c) 1))))
(define value (subr pure (t) int) (lambda (c) (down-t c)))
