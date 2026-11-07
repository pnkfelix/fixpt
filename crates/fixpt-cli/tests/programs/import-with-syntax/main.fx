;; The file's `clamp2` (its hidden `twice` of its `clamp`) of 100, its
;; `limit` 10 whatever this program's top level or a local calls `limit`:
;; 2000, and the local's 99.
(define lib (load-module "lib.fx"))
(import-with-syntax lib)
(define limit int 3)
(let ((limit 99)) (+ (* 100 (clamp2 (+ limit 1))) limit))
