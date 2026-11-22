;; A file over the bundle, which gives out a value of the type a member of it
;; has, `(select (with env m-base) t)`: in its own type, `(select (with $1
;; m-base) t)`, the argument's member's at each application.
(module-parameters ((env (load-moduleof "dm-penv.fx") qualified)))
(hide (include (with env m-base)))
(define start t (next zero))
