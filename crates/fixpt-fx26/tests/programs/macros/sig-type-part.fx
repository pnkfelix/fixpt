;; ! a part that is a description is written `desc`, not `type`
;; A part that is a description, written as it once was.
(define-syntax the-int
  (macro (type expr) expr)
  (syntax-rules ((_ t e) (the t e))))
