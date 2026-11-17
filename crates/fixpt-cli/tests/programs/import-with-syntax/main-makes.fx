;; A made macro, used by an importer: its `limit` the file's, 10, not the
;; importer's: (10 3 10).
(define m (load-module "makes.fx"))
(import-with-syntax m)
(list (let ((limit 100)) (clamp 50)) (clamp 3) (with m clamped))
