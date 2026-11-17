;; A global of the name of a macro a later import brings, made by a use in
;; the file (TODO §287): refused, as for one the file writes.
(define clamp int 1)
(define m (load-module "makes.fx"))
(import-with-syntax m)
clamp
