;; => (11 20)
;; Each `e` in its own repetition's `v`'s scope alone, as its signature says.
(define-syntax m
  (macro (letrec-shape ((pair (each (v @ bvar e @ expr) (bind v in e))))
           (_ pair ...))
         expr)
  (syntax-rules
    ((_ (v e) ...) (list ((lambda ((v int)) e) 10) ...))))
(m (a (+ a 1)) (b (* b 2)))
