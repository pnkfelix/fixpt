;; => 35
;; A hidden constant, type and module included, used by what is shown.
(define helpers (module (define twice (subr pure (int) int) (lambda (n) (* 2 n)))))
(define m
  (module
    (hide (define secret int 7)
          (define-type cell int)
          (include helpers))
    (define shown cell (twice secret))
    (define get (subr pure () int) (lambda () (+ shown secret)))))
(+ (with m shown) ((with m get)))
