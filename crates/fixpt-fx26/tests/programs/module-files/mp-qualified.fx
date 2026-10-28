;; A module parameter not included, `qualified`: its names reached by
;; `with`, or named by `import`.
(module-parameters ((m-base (load-moduleof "mp-base.fx") qualified)))
(hide (import m-base twice))
(define* four (subr pure () int) (lambda () (twice 2)))
(define* six (subr pure () int) (lambda () ((with m-base twice) 3)))
