;; A file that loads itself (`TODO.md` §71): see `modules/load-cycle.fx`.
(define me (load-module "load-cycle-self.fx"))
(define x int 1)
