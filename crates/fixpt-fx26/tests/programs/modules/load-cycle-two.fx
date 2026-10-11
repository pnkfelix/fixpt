;; ! cycle-a.fx`, 2:11: in `cycle-b.fx`, 2:11: a load cycle: `../module-files/cycle-a.fx` loads
;; Two files loading each other are refused, the chain named, and said in
;; each file on the way (`TODO.md` §§71, 73): placing it ends, though the
;; files load each other.
(define a (load-module "../module-files/cycle-a.fx"))
0
