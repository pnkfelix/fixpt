;; ! `bad`'s transformer
;; A transformer is checked where it is defined, at its style's type.
(define-syntax bad (er-macro-transformer (lambda (form rename) form)))
