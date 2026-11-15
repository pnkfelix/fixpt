;; => 7
;; A procedural macro whose contract says its uses define a macro, of a
;; signature: its expansion held to it.
(define-syntax def-const-macro
  (-> (bvar expr) (defn (A (syntax (-> () expr)))))
  (er-macro-transformer
    (lambda (form rename compare)
      `(,(rename 'define-syntax) ,(car (cdr form))
         (,(rename 'syntax-rules) ((_) ,(car (cdr (cdr form)))))))))
(def-const-macro seven 7)
(seven)
