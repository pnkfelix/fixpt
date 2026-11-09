;; => 2
;; A name, which runs nothing, may be placed under more ellipses than the
;; pattern has it: copied into each repetition.
(define dbl (subr pure (int) int) (lambda (x) (* 2 x)))
(define-syntax map-call
  (id expr ...)
  (syntax-rules ()
    ((_ f e ...) (list (f e) ...))))
(car (map-call dbl 1 2))
