;; The top layer: the bottom instance re-exported from the middle one, and
;; its type and effect selected from it.
(module-parameters ((s region)))
(define p ((proj (load-module "layer2.fx") s)))
(define rd (with p rd))
(define-type cell (select rd cell))
(define-effect own (select rd own))
(define bump (with rd bump))
(define twice (with p twice))
(define thrice (subr own () int) (lambda () (begin (twice) (bump))))
(define peek (subr (read s) (cell) int) (lambda (x) (get x)))
