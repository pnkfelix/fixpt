;; A file's own macro with a typed hole, used in the file: not yet.
(define-syntax id1 (macro ((expr #:type int)) expr) (syntax-rules ((_ e) e)))
(define x int (id1 3))
