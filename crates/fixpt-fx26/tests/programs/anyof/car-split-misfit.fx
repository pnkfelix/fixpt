;; ! argument 1 is a (oneof int string)
;; A member the call does not fit: no splitting helps, and the call's own
;; error stands.
(define f (subr pure ((oneof int string)) int) (lambda (s) (string-length s)))
