(define tag (make-continuation-prompt-tag))
(define held #f)
(call-with-continuation-prompt
  (lambda ()
    (with-continuation-mark 'ctx 'here
      (+ 100 (call-with-composable-continuation
               (lambda (k) (set! held k) (abort-current-continuation tag 0))
               tag))))
  tag
  (lambda (v) v))
(list (continuation-mark-set->list (continuation-marks held tag) 'ctx)
      (held 1)
      (held 2)
      (* 2 (held 3)))
