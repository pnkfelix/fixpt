;; ! `nosuch` is not defined at the top level
;; A renamed name the expansion leaves free is the top level's.
(define-syntax bad
  (er-macro-transformer (lambda (form rename compare) `(,(rename 'nosuch) 1))))
(bad)
