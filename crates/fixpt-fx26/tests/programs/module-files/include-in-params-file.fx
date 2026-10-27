;; A file of parameters including a module it makes at them, using its type
;; by name (Heist's problem D).
(module-parameters ((ed region)))
(include ((proj (load-module "include-cell.fx") ed)))
(define z (listof cell ed) nil)
