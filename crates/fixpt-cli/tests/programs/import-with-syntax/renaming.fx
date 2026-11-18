;; A procedural macro, and two macros whose expansions use it: one by
;; `syntax-rules`, one by explicit renaming (Heist's report, 2026-11-18).
(define-syntax pw (macro (_ e @ expr) expr)
  (er-macro-transformer (lambda (form rename compare) (car (cdr form)))))
(define-syntax via (macro (_ e @ expr) expr) (syntax-rules ((_ e) (pw e))))
(define-syntax via-er (macro (_ e @ expr) expr)
  (er-macro-transformer (lambda (form rename compare) `(,(rename 'pw) ,(car (cdr form))))))
