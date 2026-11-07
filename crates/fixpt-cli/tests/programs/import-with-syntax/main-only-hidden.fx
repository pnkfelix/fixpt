;; A hidden macro is none of what the file gives.
(define lib (load-module "lib.fx"))
(import-with-syntax lib (only clamp2 twice))
(clamp2 1)
