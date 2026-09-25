(define-syntax look
  (ir-macro-transformer
   (lambda (form inject compare)
     `(quote ,(list (eq? (cadr form) 'x) (symbol? (cadr form)) (strip-syntax (cadr form)))))))
(look x)
