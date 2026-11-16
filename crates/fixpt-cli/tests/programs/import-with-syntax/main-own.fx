;; A file's macros used in the file itself, one made by its own use of a macro that defines one:
;; (3 10 8 8 10).
(define lib (load-module "own.fx"))
(list (with lib a) (with lib b) (with lib c) (with lib d) (with lib clamped))
