;; `(only …)` names what the file gives: `limit` was not taken.
(define lib (load-module "lib.fx"))
(import-with-syntax lib (only clamp2))
limit
