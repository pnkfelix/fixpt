;; A file's own macro with a typed hole, used in the file: not yet.
(define-syntax id1 ((expr #:type int)) (syntax-rules () ((_ e) e)))
(define x int (id1 3))
