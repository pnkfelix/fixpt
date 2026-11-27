(define base (load-module "base.fx"))
(define double (subr pure (int) int) (lambda (x) (* 2 x)))
(define doubled-id (subr pure ((select base id)) int)
  (lambda (i) (double ((with base id-number) i))))
