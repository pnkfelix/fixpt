;; => 3
;; `union`, `oneof`'s name until 2026-11-05, is read as it for now.
(define g (subr pure ((union int string)) int) (lambda (v) (if (int? v) v 0)))
(g 3)
