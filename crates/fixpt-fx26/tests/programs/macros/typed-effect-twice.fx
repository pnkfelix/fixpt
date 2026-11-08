;; ! is placed twice
;; One whose effect is not `pure` may not, unless its signature says
;; `(many …)`.
(define-syntax double ((expr #:type int)) ((_ e) (+ e e)))
(double 21)
