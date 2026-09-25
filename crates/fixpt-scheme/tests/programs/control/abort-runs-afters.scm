(define tag (make-continuation-prompt-tag))
(define log '())
(define (note x) (set! log (cons x log)))
(call-with-continuation-prompt
  (lambda ()
    (dynamic-wind (lambda () (note 'in1))
      (lambda ()
        (dynamic-wind (lambda () (note 'in2))
          (lambda () (abort-current-continuation tag 'gone))
          (lambda () (note 'out2))))
      (lambda () (note 'out1))))
  tag
  (lambda (v) (note v)))
(reverse log)
