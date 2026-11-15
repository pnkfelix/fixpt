;; => 6
;; A macro a use defines whose own definition another use makes, not read
;; before: read as a use in the round after (`lt`), its binding structure
;; then what the template's scopes are read by.
(define-syntax def-adder
  (macro (bvar (many expr)) (defn (A (macro (expr) expr))))
  (syntax-rules
    ((_ name k) (define-syntax name (syntax-rules ((_ e) (+ e k)))))))
(define-syntax def-mk
  (macro (bvar)
      (defn (A (macro (bvar)
                           (defn (A (macro ((bvar expr) (import expr (rho (AA var)))) expr)))))))
  (syntax-rules
    ((_ name)
     (define-syntax name
       (macro (bvar)
                (defn (A (macro ((bvar expr) (import expr (rho (AA var)))) expr))))
       (syntax-rules
         ((_ n) (define-syntax n (macro ((bvar expr) (import expr (rho (AA var)))) expr)
                  (syntax-rules ((_ (x e) body) (let ((x e)) body))))))))))
(define-syntax twisted
  (macro (bvar) (defn (A var)))
  (syntax-rules
    ((_ v) (begin (def-adder m 5) (def-mk mk) (mk lt) (define v (lt (y 1) (m y)))))))
(twisted six)
six
