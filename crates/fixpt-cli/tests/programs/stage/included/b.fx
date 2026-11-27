(module-parameters ((m-a (load-moduleof "a.fx") #:unqualified)))
(define-type label string)
(define show (subr pure (pt) label) (lambda (p) (int->string (* scale (extract p x)))))
