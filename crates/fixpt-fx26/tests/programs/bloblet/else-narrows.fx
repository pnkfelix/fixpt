;;; `else` sees only the variants not named, so a second tagcase inside it
;;; needs no arm for `a`.
(define-type abc (sumof (a int) (b bool) (c string)))
(define f (subr pure (abc) int)
  (lambda (v)
    (tagcase v
      (a n n)
      (else rest (tagcase rest (b x (if x 1 0)) (c s (string-length s)))))))
(+ (f (sum a 40)) (+ (f (sum b #t)) (f (sum c "x"))))
