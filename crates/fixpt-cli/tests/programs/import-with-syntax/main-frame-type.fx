(define lib (load-module "frame-type.fx"))
(import-with-syntax lib)
(extract (mk (product (n 6))) n)
