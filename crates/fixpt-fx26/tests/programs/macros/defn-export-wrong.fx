;; ! this template defines `a`, and its signature says its uses define `a`, `b`
;; A signature's export is held to what the template defines.
(define-syntax define-two
  (-> (export (bvar bvar expr) (rho (A var) (AD var))) defn)
  (syntax-rules ()
    ((_ a b e) (define a e))))
