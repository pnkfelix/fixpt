;; A module over a `dm-base.fx` module, its values of that module's `t`.
(module-parameters ((m-base (load-moduleof "dm-base.fx"))))
(define* two (subr pure () t) (lambda () (next (next zero))))
