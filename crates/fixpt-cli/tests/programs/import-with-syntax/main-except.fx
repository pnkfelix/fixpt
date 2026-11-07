;; All but the file's `clamp`: `limit` is given, and `clamp2` still uses
;; the file's `clamp`, whatever this program's is.
(define lib (load-module "lib.fx"))
(import-with-syntax lib (except clamp))
(define clamp (lambda ((x int)) (* x 1000)))
(+ (+ (clamp2 100) (clamp 1)) limit)
