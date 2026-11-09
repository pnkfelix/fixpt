;; ! `...` follows a part with no pattern variable in it under as many ellipses
(define-syntax bad
  (expr)
  (syntax-rules ()
    ((_ e) (list e 1 ...))))
1
