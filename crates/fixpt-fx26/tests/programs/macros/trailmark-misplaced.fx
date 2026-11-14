;; ! a use of `string-cases`: `((else 1) ("b" 2))` is of none of the shapes this part may have
;; An `else` clause before another: R7RS's `string-cases` would take it for
;; a test, `(string=? v else)`; its signature says `else` comes last.
(define-syntax-rec
  (string-cases ((many expr) . (mu l (oneof (((trailmark else) expr)) ((expr expr) . l))))
                (syntax-rules #:trailmarks (else)
                  ((_ v (else d)) d)
                  ((_ v (k e) . rest) (if (string=? v k) e (string-cases v . rest))))))
(let ((v "b")) (string-cases v (else 1) ("b" 2)))
