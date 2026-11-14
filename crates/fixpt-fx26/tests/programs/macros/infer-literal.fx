;; => (2 4 6)
;; A `syntax-rules`' trailmark, `in`, matched by its binding, inferred
;; `(trailmark in)`.
(define-syntax in (trailmark))
(define-syntax for-sum
  (syntax-rules #:trailmarks (in)
    ((_ x in (a ...) body) (list (let ((x a)) body) ...))))
(for-sum n in (1 2 3) (* n 2))
