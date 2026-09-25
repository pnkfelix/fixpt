(define-syntax aif
  (er-macro-transformer
   (lambda (form rename compare)
     `(,(rename 'let) ((it ,(cadr form)))
        (,(rename 'if) it ,(caddr form) ,(cadddr form))))))
(aif (assq 'b '((a 1) (b 2))) (cadr it) 'no)
