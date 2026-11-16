;; => 3
;; An untyped `expr` part where `letrec` wants a lambda: the macro promises
;; nothing, and its uses' expansions are checked (two tiers).
(define-syntax call-rec
  (macro (_ f @ bvar e @ expr) expr (bind f in e))
  (syntax-rules
    ((_ f e) (letrec ((f (subr pure (int) int) e)) (f 3)))))
(call-rec g (lambda ((n int)) n))
