;; ! a template's `define-generative` names its conversions
(define-syntax define-unit
  (-> (dvar) defn)
  (syntax-rules
    ((_ name) (define-generative name int))))
(define-unit meters)
1
