;; ! this macro's expansion does not end: its uses are 1000 deep, each in the expansion of the one before, the last of `m`, inside `m`, `m`, `m`, `m`
;; A use that changes each time it comes back: no use is one it came from,
;; and the depth says it does not end.
(define-syntax m (expr) (syntax-rules ((_ e) (m (+ e 1)))))
(m 1)
