                     (define-syntax swap!
(er-macro-transformer
 (lambda (form rename compare)
   (let ((a (cadr form)) (b (caddr form)))
     `(,(rename 'let) ((,(rename 'tmp) ,a))
        (,(rename 'set!) ,a ,b)
        (,(rename 'set!) ,b ,(rename 'tmp)))))))
