;; => 7
;; A parameter's type naming an earlier parameter: a dependent procedure,
;; whose type says `(select $1 t)` for the first parameter's `t` (M5),
;; applied where it is written.
(define c
  (module (define-generative t int)
          (define seven t (up-t 7))
          (define value (subr pure (t) int) (lambda (x) (down-t x)))))
(with c (value ((lambda ((m (moduleof (abs t type) (val seven t))) (x (select m t))) x) c seven)))
