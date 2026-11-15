;; ! is placed twice
;; One whose effect is not `pure` may not, unless its signature says
;; `(many …)`.
(define-syntax double (macro ((expr #:type int)) expr) (syntax-rules ((_ e) (+ e e))))
(double 21)
