;; `one` of the file, here and in the file: 3 and 2.
(define lib (load-module "within.fx"))
(import-with-syntax lib)
(+ (* 10 (one 2)) (with lib two))
