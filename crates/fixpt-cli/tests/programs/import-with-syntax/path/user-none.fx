;; A path through a name env.fx does not define: refused.
(module-parameters ((env (load-moduleof "env.fx"))))
(hide (import-with-syntax env::m-nope (only make-thing)))
(define one (make-thing (product (n 1))))
