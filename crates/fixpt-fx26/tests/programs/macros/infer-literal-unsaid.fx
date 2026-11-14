;; ! `in` is a trailmark, which a pattern matches where its signature writes `(trailmark in)`, and no pattern variable
;; A signature written with `syntax-rules`: its trailmarks are those it
;; writes `(trailmark name)`.
(define-syntax in (trailmark))
(define-syntax for-sum
  (bvar expr (expr ...) expr)
  (syntax-rules #:trailmarks (in)
    ((_ x in (a ...) body) (list (let ((x a)) body) ...))))
1
