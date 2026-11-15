;; => 15
;; A macro whose template defines a macro (`typed-macros.md`, "Decided: what
;; a definition macro defines, said in what it makes"): a use's part placed
;; in the defined macro's template is placed where it may be more than
;; once, so its signature says `many`.
(define-syntax def-adder
  (-> (bvar (many expr)) defn)
  (syntax-rules
    ((_ name k) (define-syntax name (syntax-rules ((_ e) (+ e k)))))))
(def-adder add5 5)
(add5 10)
