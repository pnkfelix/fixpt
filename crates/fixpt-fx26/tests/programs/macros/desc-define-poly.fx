;; => 3
;; A definition's `poly`'s binders are in scope in what it is defined as,
;; the template's made fresh in both: not the top level's `a`.
(define-type a bool)
(define-syntax def-id
  (-> (bvar) defn)
  (syntax-rules ()
    ((_ name) (define name (poly ((a type)) (subr pure (a) a)) (lambda ((x a)) x)))))
(def-id ident)
((proj ident int) 3)
