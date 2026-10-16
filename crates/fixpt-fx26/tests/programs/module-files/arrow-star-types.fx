;; Types and an effect another module file imports (`arrow-star-uses.fx`).
(module-parameters ((r region)))
(define-type t int)
(define-effect e (maxeff (read r) spin))
