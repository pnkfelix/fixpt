;; ! `e` is placed under more ellipses than the pattern has it
;; An expression placed in each repetition would run each time.
(define-syntax bad
  (expr expr ...)
  ((_ e r ...) (list (+ e r) ...)))
1
