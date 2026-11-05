; Rejected: a union is below another only if each member is below it: `string`
; is not below `(oneof int symbol)`.
(define* narrow (subr pure ((oneof int string)) (oneof int symbol)) (lambda (x) x))
