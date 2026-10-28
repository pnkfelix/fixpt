;; A file of a module parameter typed by one of no parameters.
(module-parameters ((m-a (load-moduleof "mp-none.fx"))))
(define get-n (subr (read @heap) () int) (lambda () (get n)))
