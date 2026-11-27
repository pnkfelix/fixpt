;; A file of one parameter, the module `dm-env.fx` makes, at the type
;; `load-moduleof` gives it: where a chain of parameters was.
(module-parameters ((env (load-moduleof "dm-env.fx") #:unqualified)))
(define* three (subr pure () int)
  (lambda () (with env (with base (value (next ((with user two))))))))
