(define lib (load-module "macros-only.fx"))
(import-with-syntax lib)
(twice 5)
