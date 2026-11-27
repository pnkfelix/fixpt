;; A client of the bundle, taking it as its one parameter.
(module-parameters ((m-ab (load-moduleof "ifm-ab.fx") #:qualified)))
(hide (define core m-ab::core))
(hide (import core wrap (type u)))
(define x41 (subr pure () int) (lambda () (extract (extract (wrap 41) inner) x)))
