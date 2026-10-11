;; ! in `../module-files/deep-c.fx`, 3:11: in `deep-d.fx`, 2:11: cannot read `nowhere.fx`
;; A file not there, loaded two loads deep, is said so in each file on the
;; way (`TODO.md` §73).
(define c (load-module "../module-files/deep-c.fx"))
0
