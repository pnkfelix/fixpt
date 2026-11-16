;; ! `v` is a repeated part's: `(v ...)`, every repetition's, or a fact under `...`, each repetition's
;; A repeated part's label named alone by a fact not under `...`: which
;; repetition's is not said.
(define-syntax m
  (macro (_ body @ expr (v @ bvar e @ expr) ...) expr
    (bind v in body))
  (syntax-rules ((_ body (v e) ...) (let ((v e) ...) body))))
