; Rejected: a `typecase`'s arms narrow only after their tests: an arm for `int`
; leaves `x` a `(union string symbol)` in the `else`, no `string`.
(define* f (subr pure ((union int string symbol)) int)
  (lambda (x) (typecase x (int n n) (else (string-length x)))))
