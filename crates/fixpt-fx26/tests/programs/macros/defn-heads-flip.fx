;; ! this template's scopes have no one reading: `(m 2)`, headed by `m`, is read as a use of the macro a use before it defines and then as an application
;; A head read as a macro's use, then, once a use around it is read as one
;; of a macro that binds its name, as an application: refused.
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
    ((_ v) (begin (def-adder m 5) (def-mk mk) (mk lt) (define v (lt (m 1) (m 2)))))))
