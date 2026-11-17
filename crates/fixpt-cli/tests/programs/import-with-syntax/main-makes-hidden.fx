;; A macro made in a `hide` is not given on: refused, `cap` unbound.
(define m (load-module "makes.fx"))
(import-with-syntax m)
(cap 50)
