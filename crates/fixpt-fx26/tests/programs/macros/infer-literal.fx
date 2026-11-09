;; => (2 4 6)
;; A `syntax-rules`' literal, `in`, written as it is: `(literal in)`.
(define-syntax for-sum
  (syntax-rules (in)
    ((_ x in (a ...) body) (list (let ((x a)) body) ...))))
(for-sum n in (1 2 3) (* n 2))
