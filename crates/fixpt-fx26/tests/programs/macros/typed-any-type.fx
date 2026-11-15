;; => 5
;; A hole's type left out: the template checked for any type.
(define-syntax same (macro ((expr #:effect pure)) expr) (syntax-rules ((_ e) (if #t e e))))
(same 5)
