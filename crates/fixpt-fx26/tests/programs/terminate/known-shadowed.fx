; Rejected: inside `omega`, `w` is the parameter, not the known `w` above,
; so `(w w)` may loop and must say `spin` (docs/research/
; soundness-findings.md, F1).
(define-type T (subr pure (T) int))
(define w T (lambda (x) 0))
(define omega T (lambda ((w T)) (w w)))
