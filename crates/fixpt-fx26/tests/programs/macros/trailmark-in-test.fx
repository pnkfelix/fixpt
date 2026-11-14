;; ! `k` is placed where its syntax type is not one the form takes there
;; A clause's head that may be `else` placed as an expression: refused, as
;; `(string=? v else)` would be.
(define-syntax-rec
  (string-cases (expr ((oneof (trailmark else) expr) expr) ...)
                (syntax-rules #:trailmarks (else)
                  ((_ v (else d)) d)
                  ((_ v (k e) c ...) (if (string=? v k) e (string-cases v c ...))))))
1
