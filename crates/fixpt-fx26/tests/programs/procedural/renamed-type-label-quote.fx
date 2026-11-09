;; => 5
;; A renamed type, label and quoted name are each the name: a label and a
;; quoted symbol bind nothing; a type name free in the expansion is the top
;; level's.
(define-syntax tagged
  (er-macro-transformer
    (lambda (form rename compare)
      `(,(rename 'the) (,(rename 'sumof) (,(rename 'num) ,(rename 'int)))
         (,(rename 'sum) ,(rename 'num) ,(car (cdr form)))))))
(define-syntax quoted
  (er-macro-transformer (lambda (form rename compare) `(,(rename 'quote) ,(rename 'hello)))))
(if (symbol=? (quoted) 'hello) (tagcase (tagged 5) (num n n)) 0)
