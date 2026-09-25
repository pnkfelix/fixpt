(define-syntax aif
  (ir-macro-transformer
   (lambda (form inject compare)
     `(let ((,(inject 'it) ,(cadr form)))
        (if ,(inject 'it) ,(caddr form) ,(cadddr form))))))
