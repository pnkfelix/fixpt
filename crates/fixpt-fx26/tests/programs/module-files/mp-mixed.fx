;; A region and a module: the `plambda` over the region, then the
;; `lambda` over the module.
(module-parameters ((r region) (m-base (load-moduleof "mp-base.fx"))))
(define* cell (subr (alloc r) (int) (ref int r)) (lambda (n) (new (twice n))))
