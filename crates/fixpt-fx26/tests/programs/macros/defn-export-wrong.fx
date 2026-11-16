;; ! this template defines `a`, and its signature says its uses define `a`, `b`
;; A signature's export is held to what the template defines.
(define-syntax define-two
  (macro (_ a @ bvar b @ bvar expr) (defn a b))
  (syntax-rules
    ((_ a b e) (define a e))))
