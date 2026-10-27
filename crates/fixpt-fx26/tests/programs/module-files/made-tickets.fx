;; A function of a scheduler, only as much of one as it uses (`restrict`).
(plambda ((ed region) (world effect))
  (lambda ((core (restrict (load-moduleof "made-core.fx" ed world) issue number)))
    (module
      (define next (subr (maxeff (read ed) (write ed)) () int)
        (lambda () ((with core number) ((with core issue))))))))
