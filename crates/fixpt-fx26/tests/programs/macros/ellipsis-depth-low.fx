;; ! `e` is placed under 0 ellipses, and the pattern has it under 1
(define-syntax bad
  (expr ...)
  (syntax-rules ()
    ((_ e ...) (list e))))
1
