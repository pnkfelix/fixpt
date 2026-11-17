;; => 1
;; A `let` of a path to a module keeps the path's types: `m` is `counter`,
;; and its `t` is `counter..t`.
(define counter
  (module
    (define-generative t int #:seal up-t #:unseal down-t)
    (define zero t (up-t 0))
    (define inc (subr pure (t) t) (lambda (c) (up-t (+ (down-t c) 1))))
    (define value (subr pure (t) int) (lambda (c) (down-t c)))))
(let ((m counter)) ((with counter value) ((with m inc) (with counter zero))))
