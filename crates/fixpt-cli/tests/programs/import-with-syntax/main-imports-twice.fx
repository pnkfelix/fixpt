(define m (load-module "imports-twice.fx"))
(import-with-syntax m)
(twice 5)
