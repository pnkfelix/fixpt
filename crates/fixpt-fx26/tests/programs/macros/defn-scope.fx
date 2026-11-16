;; => 7
;; The second expression in the scope of the first name, as the signature
;; says (Herman's import): the use's `b` may name `a`.
(define-syntax define-both
  (macro (_ a @ bvar expr bvar e2 @ expr) defn (bind a in e2))
  (syntax-rules
    ((_ a e1 b e2) (begin (define a e1) (define b e2)))))
(define-both a 3 b (+ a 1))
(+ a b)
