;; => 1
;; A definition an expansion names by an alias is a global of its own, which
;; nothing the program wrote can name.
(define-syntax counter
  (er-macro-transformer
    (lambda (form rename compare)
      `(,(rename 'begin) (,(rename 'define) ,(rename 'n) 1) ,(rename 'n)))))
(counter)
