;; A module file's import, used in it and given on: `clamp` the file
;; `lib.fx`'s, its `limit` 10 whatever the importer's: (6 10 10).
(define m (load-module "imports-in-file.fx"))
(import-with-syntax m)
(define limit int 1000)
(list (with m (g 5)) (with m (g 50)) (clamp 99))
