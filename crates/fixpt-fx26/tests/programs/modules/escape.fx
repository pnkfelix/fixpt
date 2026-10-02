;; ! not known outside the scope where the module is named
;; A module's abstract type may not leave the scope of its name.
(define counter
  (module
    (define-generative t int)
    (define zero t (up-t 0))
    (define inc (subr pure (t) t) (lambda (c) (up-t (+ (down-t c) 1))))
    (define value (subr pure (t) int) (lambda (c) (down-t c)))))
(let ((m counter)) (with m zero))
