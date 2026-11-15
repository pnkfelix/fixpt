;; => 17
;; A transformer that names a binder of its own after its use's, `y-tmp` of
;; `y`: the two runs bind differently named names alike, so its expansion
;; is the same up to its binders' names, and kept.
(define-syntax let1
  (-> ((bvar expr) (import expr (rho (AA var)))) expr)
  (er-macro-transformer
    (lambda (form rename compare)
      (let* ((xe (car (cdr form))) (body (car (cdr (cdr form)))) (b (car xe))
             (tmp (if (symbol? b) (string->symbol (string-append (symbol->string b) "-tmp")) 't)))
        `(,(rename 'let) ((,b ,(car (cdr xe))))
           (,(rename 'let) ((,tmp 10)) (,(rename '+) ,body ,tmp)))))))
(let1 (y 3) (+ y 4))
