;; => 21
;; A template that uses a macro whose uses define a macro, then that macro:
;; read as its use, by the signature said (`typed-macros.md`, "Decided: a
;; template's heads read by their scope, to a fixed point").
(define-syntax def-adder
  (macro (_ name @ bvar (many expr)) (defn (name (macro (_ expr) expr))))
  (syntax-rules
    ((_ name k) (define-syntax name (syntax-rules ((_ e) (+ e k)))))))
(define-syntax def-both
  (macro (_ v @ bvar m @ bvar) (defn v (m (macro (_ expr) expr))))
  (syntax-rules
    ((_ v m) (begin (def-adder m 5) (define v (m 10))))))
(def-both fifteen add5)
(+ fifteen (add5 1))
