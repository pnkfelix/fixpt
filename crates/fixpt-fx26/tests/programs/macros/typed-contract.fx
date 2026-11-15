;; ! a int is expected here, and this is a bool
;; A use's expression is held to its hole's type, `(the T e)`.
(define-syntax id1 (macro ((expr #:type int)) expr) (syntax-rules ((_ e) e)))
(id1 #t)
