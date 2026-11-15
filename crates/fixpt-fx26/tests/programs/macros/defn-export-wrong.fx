;; ! this template defines `a`, and its signature says its uses define `a`, `b`
;; A signature's export is held to what the template defines.
(define-syntax define-two
  (macro (bvar bvar expr) (defn (A var) (AD var)))
  (syntax-rules
    ((_ a b e) (define a e))))
