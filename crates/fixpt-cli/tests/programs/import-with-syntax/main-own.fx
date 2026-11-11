;; A file's macros used in the file itself: (3 10 8 8).
(define lib (load-module "own.fx"))
(list (with lib a) (with lib b) (with lib c) (with lib d))
