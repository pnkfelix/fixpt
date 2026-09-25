(define-syntax ir-swap!
  (ir-macro-transformer
   (lambda (form inject compare)
     `(let ((tmp ,(cadr form))) (set! ,(cadr form) ,(caddr form)) (set! ,(caddr form) tmp)))))
(define tmp 1) (define other 2) (ir-swap! tmp other) (list tmp other)
