;; ! `payload` makes a description, not an expression
(define-syntax payload (-> (type) type) (syntax-rules () ((_ f) f)))
(define-syntax bad (expr) (syntax-rules () ((_ e) (payload e))))
1
