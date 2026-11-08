;; ! `payload` makes a description, not an expression
(define-syntax payload (-> (type) type) ((_ f) f))
(define-syntax bad (expr) ((_ e) (payload e)))
1
