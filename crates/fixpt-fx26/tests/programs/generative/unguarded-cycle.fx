; Rejected: `wrap`'s representation is what it is given, so `T` is `T`
; again, with no constructor between (docs/research/soundness-findings.md,
; A2).
(define-generative (wrap (a type +)) a)
(define-type T (wrap T))
