;; => 6
;; A macro a use defines whose own definition another use makes, not read
;; before: read as a use in the round after (`lt`), its binding structure
;; then what the template's scopes are read by.
(define-syntax def-adder
  (macro (_ name @ bvar (many expr)) (defn (name (macro (_ expr) expr))))
  (syntax-rules
    ((_ name k) (define-syntax name (syntax-rules ((_ e) (+ e k)))))))
(define-syntax def-mk
  (macro (_ name @ bvar)
         (defn (name (macro (_ n @ bvar)
                            (defn (n (macro (_ (x @ bvar e @ expr) body @ expr) expr
                                       (bind x in body))))))))
  (syntax-rules
    ((_ name)
     (define-syntax name
       (macro (_ n @ bvar)
              (defn (n (macro (_ (x @ bvar e @ expr) body @ expr) expr (bind x in body)))))
       (syntax-rules
         ((_ n) (define-syntax n (macro (_ (x @ bvar e @ expr) body @ expr) expr (bind x in body))
                  (syntax-rules ((_ (x e) body) (let ((x e)) body))))))))))
(define-syntax twisted
  (macro (_ v @ bvar) (defn v))
  (syntax-rules
    ((_ v) (begin (def-adder m 5) (def-mk mk) (mk lt) (define v (lt (y 1) (m y)))))))
(twisted six)
six
