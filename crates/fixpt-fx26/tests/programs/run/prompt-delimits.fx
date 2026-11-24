;; => 23
;; A prompt drops its own transfers of control to its tag's region only
;; where nothing but its tag reaches the region (`Checker::reaches_only`;
;; the cell verifier's `prompt_delimits`, TODO §117): `own`'s body names
;; only `u`, so its type says none; `other`'s inner prompt's body names
;; `v`, another tag in @p, and aborts to it past that prompt, so its type
;; keeps them.
(define-effect tags (read (globals u v)))
(define u (prompt-tag int int tags @p) (make-continuation-prompt-tag))
(define v (prompt-tag int int tags @p) (make-continuation-prompt-tag))
(define* own (subr (read (globals u)) (int) int)
  (lambda (x)
    (prompt u
            (+ 1 ((proj (proj abort-current-continuation @p) int int tags) u (* x 2)))
            (lambda ((y int)) y))))
(define* other (subr (maxeff (goto @p) (read (globals u v))) (int) int)
  (lambda (x)
    (prompt v
            (prompt u
                    (+ 1 ((proj (proj abort-current-continuation @p) int int tags) v x))
                    (lambda ((y int)) y))
            (lambda ((y int)) (+ y 10)))))
(+ (own 3) (other 7))
