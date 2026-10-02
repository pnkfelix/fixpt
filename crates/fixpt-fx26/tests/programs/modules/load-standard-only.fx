;; ! in `../module-files/uses-global.fx`, 3:18: unbound variable `secret`
;; A module read from a file sees only the standard environment, not the
;; program's globals: so it means the same wherever it is read.
(define secret int 41)
(load-module "../module-files/uses-global.fx")
