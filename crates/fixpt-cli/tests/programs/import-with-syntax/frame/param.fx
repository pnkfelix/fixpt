(module-parameters ((m-core (load-moduleof "core.fx"))))
(hide (define own int 2))
(define-syntax act (macro (_ e @ expr) expr)
  (syntax-rules ((_ e) (+ (core-helper e) own))))
