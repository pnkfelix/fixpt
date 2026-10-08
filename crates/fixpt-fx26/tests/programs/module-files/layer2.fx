;; The middle layer: loads the bottom, re-exports from it.
(module-parameters ((s region)))
(define rd ((proj (load-module "layer1.fx") s)))
(define-effect own (select rd own))
(define bump (with rd bump))
(define twice (subr own () int) (lambda () (begin (bump) (bump))))
