(define tag (make-continuation-prompt-tag))
(call-with-continuation-prompt
  (lambda () (+ 1 (abort-current-continuation tag 10 20)))
  tag
  (lambda (a b) (list 'handled a b)))
