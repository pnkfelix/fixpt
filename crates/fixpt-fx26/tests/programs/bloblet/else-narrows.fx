;;; `else` sees only the variants not named, so a second tagcase inside it
;;; needs no arm for `a`.
(define-type abc (oneof (a int) (b bool) (c string)))
(define f (subr pure (abc) int)
  (lambda (v)
    (tagcase v
      (a n n)
      (else rest (tagcase rest (b x (if x 1 0)) (c s (string-length s)))))))
(+ (f (one a 40)) (+ (f (one b #t)) (f (one c "x"))))
