;; ! `in` is among the `syntax-rules` literals, and the signature has a part here, not `(literal in)`
;; A signature written with `syntax-rules`: its literals are those it
;; writes as they are.
(define-syntax for-sum
  (bvar expr (expr ...) expr)
  (syntax-rules (in)
    ((_ x in (a ...) body) (list (let ((x a)) body) ...))))
1
