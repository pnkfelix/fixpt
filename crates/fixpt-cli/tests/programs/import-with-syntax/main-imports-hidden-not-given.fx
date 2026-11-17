;; A hidden import's macros are not given on: refused, `twice` unbound.
(define m (load-module "imports-hidden.fx"))
(import-with-syntax m)
(twice 5)
