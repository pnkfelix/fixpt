; Rejected: a union is below another only if each member is below it: `string`
; is not below `(union int symbol)`.
(define* narrow (subr pure ((union int string)) (union int symbol)) (lambda (x) x))
