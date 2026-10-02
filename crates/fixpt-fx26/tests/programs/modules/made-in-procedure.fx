;; => 42
;; A procedure that makes a module, as a functor would; its register code
;; makes it too.
(define-type counters
  (moduleof (abs t type) (val zero t) (val inc (subr pure (t) t)) (val value (subr pure (t) int))))
(define make (subr pure (int) counters)
  (lambda (start)
    (module
      (define-generative t int)
      (define zero t (up-t start))
      (define-rec
        (inc (subr pure (t) t) (lambda (c) (up-t (+ (down-t c) 1))))
        (value (subr pure (t) int) (lambda (c) (down-t c)))))))
(define use (subr pure (counters) int)
  (lambda (c) (with c (value (inc (inc zero))))))
(use (make 40))
