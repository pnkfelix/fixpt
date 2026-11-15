;; ! `payload` makes a description, not an expression
(define-syntax payload (-> (desc) desc) (syntax-rules ((_ f) f)))
(define-syntax bad (-> (expr) expr) (syntax-rules ((_ e) (payload e))))
1
