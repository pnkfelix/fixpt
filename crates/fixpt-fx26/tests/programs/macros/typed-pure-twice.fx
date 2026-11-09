;; => 42
;; A hole of no effect may be placed twice: running it twice does nothing
;; twice.
(define-syntax double ((expr #:type int #:effect pure)) (syntax-rules () ((_ e) (+ e e))))
(double 21)
