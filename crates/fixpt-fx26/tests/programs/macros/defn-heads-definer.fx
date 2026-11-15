;; => 4
;; The defined macro makes definitions: where a definition is, its use read
;; as one, what it defines seen after it; its name the template's own.
(define-syntax def-definer
  (-> (bvar) (defn (A (syntax (-> (bvar expr) (defn (A var)))))))
  (syntax-rules
    ((_ name) (define-syntax name (syntax-rules ((_ x e) (define x e)))))))
(define-syntax via
  (-> (bvar) (defn (A var)))
  (syntax-rules
    ((_ v) (begin (def-definer my-def) (my-def w 3) (define v (+ w 1))))))
(via four)
four
