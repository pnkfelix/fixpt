;; => 9
;; A definitions contract's names in the scope of the definitions after
;; them, as the expansion has them; its expression in neither.
(define-syntax define-pair
  (-> (bvar bvar expr) (defn (A var) (AD var)))
  (er-macro-transformer
    (lambda (form rename compare)
      (let ((a (car (cdr form))) (b (car (cdr (cdr form)))) (e (car (cdr (cdr (cdr form))))))
        `(,(rename 'begin) (,(rename 'define) ,a int ,e)
                           (,(rename 'define) ,b int (,(rename '+) ,a 1)))))))
(define four int 4)
(define-pair four-again five four)
(+ four-again five)
