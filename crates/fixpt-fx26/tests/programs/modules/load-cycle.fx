;; ! a load cycle: `../module-files/load-cycle-self.fx` loads `load-cycle-self.fx`
;; A file that loads itself, or one that loads it, is refused, the chain
;; named (`TODO.md` §71): it was read again for each load, without end.
(define m (load-module "../module-files/load-cycle-self.fx"))
(with m x)
