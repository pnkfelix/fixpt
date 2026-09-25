(define tag (make-continuation-prompt-tag))
(define seen '())
(call-with-continuation-prompt
  (lambda ()
    (with-exception-handler (lambda (e) 'outer-handler)
      (lambda ()
        (with-continuation-mark 'm 'outer-mark
          (dynamic-wind
            (lambda () #f)
            (lambda ()
              (with-exception-handler (lambda (e) 'inner-handler)
                (lambda ()
                  (with-continuation-mark 'm 'inner-mark
                    (car (list (abort-current-continuation tag 'x)))))))
            (lambda ()
              (set! seen (list (raise-continuable 'probe)
                               (continuation-mark-set-first #f 'm)))))))))
  tag
  (lambda (v) v))
seen
