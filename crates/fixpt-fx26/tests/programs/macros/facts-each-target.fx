;; ! a fact binding in a repeated part is each repetition's: followed by `...`
;; A fact not under `...` binding in a repeated part: which repetition's is
;; not said.
(define-syntax m
  (macro (_ (v @ bvar e @ expr) ...) expr
    (bind (v ...) in e))
  (syntax-rules ((_ (v e) ...) (list e ...))))
