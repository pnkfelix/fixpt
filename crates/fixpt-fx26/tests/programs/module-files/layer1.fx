;; The bottom of three layers of module files of a region parameter.
(module-parameters ((s region)))
(define-effect own (maxeff (read s) (write s)))
(define-type cell (ref int s))
(define c cell (new 0))
(define bump (subr own () int) (lambda () (begin (set c (+ (get c) 1)) (get c))))
