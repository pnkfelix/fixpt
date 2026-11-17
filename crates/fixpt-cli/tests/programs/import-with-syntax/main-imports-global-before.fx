;; A global of the name of a macro a later import brings, given on by the
;; file's own import: refused where it is defined, as for one the file
;; writes.
(define clamp int 1)
(define m (load-module "imports-in-file.fx"))
(import-with-syntax m)
clamp
