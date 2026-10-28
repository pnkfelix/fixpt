;; A file of a module parameter (Heist's, 2026-10-28): `mp-base.fx`'s names
;; its own, hidden; loaded as `((load-module "mp-buffer.fx") m-base)`.
(module-parameters ((m-base (load-moduleof "mp-base.fx"))))
(define tally (ref int @c) (new 0))
;; Expressions, run in order as the module is made.
(set tally (+ (get tally) (twice 5)))
(set tally (+ (get tally) 1))
(define* seen (subr (read @c) () int) (lambda () (get tally)))
(define* origin (subr pure () pt) (lambda () (product (x 0) (y (twice 2)))))
