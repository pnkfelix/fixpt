;; ! where a zeros is expected
;; Module types match exactly: a module of other values is not one.
(define counter
  (module
    (define-generative t int)
    (define zero t (up-t 0))
    (define inc (subr pure (t) t) (lambda (c) (up-t (+ (down-t c) 1))))
    (define value (subr pure (t) int) (lambda (c) (down-t c)))))
(define-type zeros (moduleof (abs t type) (val zero t)))
(define use (subr pure (zeros) int) (lambda (m) 0))
(use counter)
