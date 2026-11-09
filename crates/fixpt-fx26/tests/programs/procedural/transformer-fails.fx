;; ! its transformer: car or cdr of a non-pair
;; A transformer that fails, as it runs at a use, says so there.
(define-syntax second
  (er-macro-transformer (lambda (form rename compare) (car (cdr (cdr form))))))
(second 1)
