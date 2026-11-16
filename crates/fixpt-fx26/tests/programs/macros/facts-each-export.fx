;; ! a fact under `...` is a `bind`, each repetition's
;; What a list exports is every repetition's, `(export (x ...))`, not a
;; fact under `...`.
(define-syntax-rec
  (m (macro (letrec-shape ((bs (b ((v @ bvar e @ expr) ...) (export v) ...)))
              (_ x @ bs body @ expr))
            expr
       (bind x in body))
     (syntax-rules ((_ ((v e) ...) body) (let ((v e) ...) body)))))
