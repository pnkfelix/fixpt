;; The file's `define-clamped`: `big` is the file's `limit`, 10, whatever
;; this program calls `limit` and `raw`: 18.
(define defns (load-module "defns.fx"))
(import-with-syntax defns)
(define limit int 3)
(define raw int 5)
(define-clamped big 50)
(+ big (+ limit raw))
