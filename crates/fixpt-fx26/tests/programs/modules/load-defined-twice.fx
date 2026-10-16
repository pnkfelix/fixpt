;; ! in `../module-files/defines-twice.fx`, 1:1: `t` is defined twice in this module
;; A module's file that defines a name twice is refused, as a `module` form
;; is, and said in the file, as its other errors are: both checkers once
;; said it at different places, neither in the file.
(define m (load-module "../module-files/defines-twice.fx"))
0
