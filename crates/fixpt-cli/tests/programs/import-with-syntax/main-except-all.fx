;; All but `limit` is the file's macros alone: the `include` gives nothing.
(define lib (load-module "lib.fx"))
(import-with-syntax lib (except limit))
(clamp2 1)
