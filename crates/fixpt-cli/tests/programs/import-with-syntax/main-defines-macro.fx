;; The file's `define-clamper`: `clamp`'s `limit` is the file's, 10,
;; whatever this program calls `limit`: 13.
(define defines (load-module "defines-macro.fx"))
(import-with-syntax defines)
(define limit int 3)
(define-clamper clamp)
(+ (clamp 50) limit)
