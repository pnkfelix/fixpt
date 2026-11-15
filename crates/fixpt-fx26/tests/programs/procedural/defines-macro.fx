;; => 7
;; A procedural macro's expansion that defines a macro, for the forms after.
(define-syntax def-const-macro
  (er-macro-transformer
    (lambda (form rename compare)
      `(,(rename 'define-syntax) ,(car (cdr form))
         (,(rename 'syntax-rules) ((_) ,(car (cdr (cdr form)))))))))
(def-const-macro seven 7)
(seven)
