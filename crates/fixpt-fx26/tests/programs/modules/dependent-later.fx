;; ! dependent type, not supported yet
;; A parameter's type naming another parameter waits for stage M5.
(define counter
  (module
    (define-generative t int)
    (define zero t (up-t 0))
    (define inc (subr pure (t) t) (lambda (c) (up-t (+ (down-t c) 1))))
    (define value (subr pure (t) int) (lambda (c) (down-t c)))))
(lambda ((m (moduleof (abs t type) (val zero t))) (x (select m t))) x)
