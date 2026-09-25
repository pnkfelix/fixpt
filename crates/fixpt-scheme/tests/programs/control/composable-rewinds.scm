(define tag (make-continuation-prompt-tag))
(define log '())
(define (note x) (set! log (cons x log)))
(define held #f)
(call-with-continuation-prompt
  (lambda ()
    (dynamic-wind (lambda () (note 'in))
      (lambda ()
        (call-with-composable-continuation
          (lambda (k) (set! held k) (abort-current-continuation tag 'stop))
          tag))
      (lambda () (note 'out))))
  tag
  (lambda (v) (note v)))
(note (held 'again))
(reverse log)
