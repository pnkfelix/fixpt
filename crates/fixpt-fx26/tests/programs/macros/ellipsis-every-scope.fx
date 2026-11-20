;; ! `e` is placed in the scope of `(v ...)`, but its signature says it is in the scope of `v`
;; A binder under an ellipsis: its own repetition's, or every one's
;; (`TODO.md` §223). The signature says each `e` sees its own `v`; the
;; template puts every `e` in every `v`'s scope.
(define-syntax m
  (macro (_ (v @ bvar e @ expr) ...) expr
    (bind v in e) ...)
  (syntax-rules
    ((_ (v e) ...) ((lambda ((v int) ...) (list e ...)) 1 ...))))
(m (a b) (b a))
