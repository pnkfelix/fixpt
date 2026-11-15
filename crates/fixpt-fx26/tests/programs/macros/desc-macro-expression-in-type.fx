;; ! `ident` makes an expression, not a description
(define-syntax ident (-> (expr) expr) (syntax-rules ((_ e) e)))
(define-syntax bad (-> (expr) expr) (syntax-rules ((_ e) (the (ident int) e))))
1
