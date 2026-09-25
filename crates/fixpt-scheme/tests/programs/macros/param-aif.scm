(define-syntax-parameter it
  (syntax-rules () (_ (syntax-error "`it` is only meaningful inside aif"))))
(define-syntax aif
  (syntax-rules ()
    ((_ test then else)
     (let ((t test))
       (syntax-parameterize ((it (identifier-syntax t)))
         (if t then else))))))
