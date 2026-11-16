;; => 12
;; A name the defined macro has, bound again by a `lambda` inside: there
;; the parameter, as its binding structure says, an application.
(define-syntax def-adder
  (macro (_ name @ bvar (many expr)) (defn (name (macro (_ expr) expr))))
  (syntax-rules
    ((_ name k) (define-syntax name (syntax-rules ((_ e) (+ e k)))))))
(define-syntax pair-of
  (macro (_ v @ bvar w @ bvar) (defn v w))
  (syntax-rules
    ((_ v w) (begin (def-adder inc 5)
                    (define v ((lambda ((inc (-> (int) int))) (inc 3)) (lambda ((x int)) (* x 2))))
                    (define w (inc 1))))))
(pair-of six also-six)
(+ six also-six)
