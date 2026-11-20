;; => 3
;; A level of several labels is one rib: `a` and `b` bound together, as `let` binds them
;; (Heist's should-work note, entry 1).
(define-syntax with2
  (macro (_ (a @ bvar b @ bvar) body @ expr) expr (bind (a b) in body))
  (syntax-rules ((_ (a b) body) (let ((a 1) (b 2)) body))))
(with2 (x y) (+ x y))
