;; A file with module parameters, loaded and not applied: no instance, whose
;; macros could name it.
(define c (load-module "counter.fx"))
(import-with-syntax c)
