; Rejected: a procedure's type may say what its result proves, but a `lambda`
; is not yet checked against one (`TODO.md` §54): its body is a `bool`, which
; proves nothing, so no procedure of the program's own can claim it.
(define* liar (subr pure ((union int string)) (bool (then (shape 0 int)) (else)))
  (lambda (x) #t))
