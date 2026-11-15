;; ! `add5` is defined already: a macro may not take its name
;; A macro an expansion defines, of a global's name.
(define-syntax def-adder
  (-> (bvar (many expr)) defn)
  (syntax-rules
    ((_ name k) (define-syntax name (syntax-rules ((_ e) (+ e k)))))))
(define add5 1)
(def-adder add5 5)
