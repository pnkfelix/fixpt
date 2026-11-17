;; `only` takes of a file's macros those it gives on too: `clamp`, alone: 10.
(define m (load-module "imports-in-file.fx"))
(import-with-syntax m (only clamp))
(clamp 50)
