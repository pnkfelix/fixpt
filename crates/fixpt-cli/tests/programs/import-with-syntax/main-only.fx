;; Only the file's `clamp2`: its `clamp` and `limit` are not this program's,
;; and `clamp2` still uses the file's `clamp`, whatever this program's is.
(define lib (load-module "lib.fx"))
(import-with-syntax lib (only clamp2))
(define clamp (lambda ((x int)) (* x 1000)))
(+ (clamp2 100) (clamp 1))
