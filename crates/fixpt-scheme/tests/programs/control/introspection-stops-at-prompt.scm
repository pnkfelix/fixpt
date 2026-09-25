(define tag (make-continuation-prompt-tag 'p))
(with-continuation-mark 'k 'outside
  (car (list
    (call-with-continuation-prompt
      (lambda ()
        (with-continuation-mark 'k 'inside
          (car (list (continuation-mark-set->list
                       (current-continuation-marks tag) 'k)))))
      tag))))
