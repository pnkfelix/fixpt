;; ! deep-a.fx`, 2:11: in `deep-b.fx`, 2:15: a int is expected here, and this is a string
;; An error in a file loaded by a file the program loads is said at the
;; program's load, then in each file on the way (`TODO.md` §73), the same
;; by both checkers.
(define a (load-module "../module-files/deep-a.fx"))
0
