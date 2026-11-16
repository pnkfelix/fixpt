;; ! `e` is placed under 0 ellipses, and the pattern has it under 1
(define-syntax bad
  (macro (_ expr ...) expr)
  (syntax-rules
    ((_ e ...) (list e))))
1
