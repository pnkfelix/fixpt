;; ! `payload` makes a description, not an expression
(define-syntax payload (macro (desc) desc) (syntax-rules ((_ f) f)))
(define-syntax bad (macro (expr) expr) (syntax-rules ((_ e) (payload e))))
1
