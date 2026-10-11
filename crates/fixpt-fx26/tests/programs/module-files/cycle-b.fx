;; A module file loading the one that loads it (`modules/load-cycle-two.fx`).
(define a (load-module "cycle-a.fx"))
