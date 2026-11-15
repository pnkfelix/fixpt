;; ! its expansion depends on how its use's bound names are spelled
;; The same transformer, its use's body naming a global `y-tmp`: the
;; transformer's own `y-tmp` captures it, and a use whose binder is spelled
;; otherwise would not.
(define-syntax let1
  (-> ((bvar expr) (import expr (rho (AA var)))) expr)
  (er-macro-transformer
    (lambda (form rename compare)
      (let* ((xe (car (cdr form))) (body (car (cdr (cdr form)))) (b (car xe))
             (tmp (if (symbol? b) (string->symbol (string-append (symbol->string b) "-tmp")) 't)))
        `(,(rename 'let) ((,b ,(car (cdr xe))))
           (,(rename 'let) ((,tmp 10)) (,(rename '+) ,body ,tmp)))))))
(define y-tmp int 100)
(let1 (y 3) (+ y y-tmp))
