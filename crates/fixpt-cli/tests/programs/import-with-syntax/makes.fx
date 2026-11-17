;; Macros a module file's own uses make (TODO §287): `clamp` given on as a
;; written one is, its `limit` this file's; `cap`, made in a `hide`, not.
(define limit int 10)
(define-syntax define-clamper (macro (_ bvar) defn)
  (syntax-rules ((_ n) (define-syntax n (syntax-rules ((_ x) (if (> x limit) limit x)))))))
(define-clamper clamp)
(hide (define-clamper cap))
(define clamped int (cap 50))
