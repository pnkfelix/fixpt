;; => "B"
;; Heist's `string-cases` (its request `literal-overlap.fx`): `else` the
;; standard trailmark, told apart from an expression by its binding, so a
;; clause's head is `(trailmark else)` or an `expr`, one signature; the
;; `else` clause last, as the type of the list says (`typed-macros.md`,
;; "Trailmarks").
(define-syntax-rec
  (string-cases ((many expr) . (mu l (oneof (((trailmark else) expr)) ((expr expr) . l))))
                (syntax-rules #:trailmarks (else)
                  ((_ v (else d)) d)
                  ((_ v (k e) . rest) (if (string=? v k) e (string-cases v . rest))))))
(let ((v "b")) (string-cases v ("a" "A") ("b" "B") (else "?")))
