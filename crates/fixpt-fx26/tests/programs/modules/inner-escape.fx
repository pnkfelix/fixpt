;; ! `z`'s type mentions `m..t`, which is not known outside the module
;; A module bound inside a module keeps its abstract types inside.
(define counter
  (module
    (define-generative t int)
    (define zero t (up-t 0))
    (define inc (subr pure (t) t) (lambda (c) (up-t (+ (down-t c) 1))))
    (define value (subr pure (t) int) (lambda (c) (down-t c)))))
(define outer (module (define m counter) (define z (with m zero))))
