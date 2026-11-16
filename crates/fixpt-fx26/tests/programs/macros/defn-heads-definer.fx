;; => 4
;; The defined macro makes definitions: where a definition is, its use read
;; as one, what it defines seen after it; its name the template's own.
(define-syntax def-definer
  (macro (_ name @ bvar) (defn (name (macro (_ p1 @ bvar expr) (defn p1)))))
  (syntax-rules
    ((_ name) (define-syntax name (syntax-rules ((_ x e) (define x e)))))))
(define-syntax via
  (macro (_ v @ bvar) (defn v))
  (syntax-rules
    ((_ v) (begin (def-definer my-def) (my-def w 3) (define v (+ w 1))))))
(via four)
four
