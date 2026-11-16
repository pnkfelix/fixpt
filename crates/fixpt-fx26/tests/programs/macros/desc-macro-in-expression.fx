;; ! `payload` makes a description, not an expression
(define-syntax payload (macro (_ desc) desc) (syntax-rules ((_ f) f)))
(define-syntax bad (macro (_ expr) expr) (syntax-rules ((_ e) (payload e))))
1
