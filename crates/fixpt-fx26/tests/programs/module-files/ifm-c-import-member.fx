;; A client of the bundle, taking it as its one parameter.
(module-parameters ((m-ab (load-moduleof "ifm-ab.fx") #:qualified)))
(hide (import m-ab m-b))
(hide (import m-b wrap (type u)))
(define x41 (subr pure () int) (lambda () (extract (extract (wrap 41) inner) x)))
