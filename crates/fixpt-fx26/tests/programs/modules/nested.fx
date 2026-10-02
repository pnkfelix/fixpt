;; => 2
;; A module of a module: opened, then opened again.
(define counter
  (module
    (define-generative t int)
    (define zero t (up-t 0))
    (define inc (subr pure (t) t) (lambda (c) (up-t (+ (down-t c) 1))))
    (define value (subr pure (t) int) (lambda (c) (down-t c)))))
(define outer
  (module (define c counter)
          (define get (subr pure () int) (lambda () (with c (value (inc (inc zero))))))))
(with outer (get))
