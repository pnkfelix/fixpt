;; ! `m` is bound as sendable, and a (ref int @c) is not: a reference at @c, which can be written
;; Refused: a `sendable` binder given what may not be sent.
(define* pass (poly ((m sendable)) (subr pure (m) m)) (plambda ((m sendable)) (lambda (x) x)))
((proj pass (ref int @c)) (new 1))
