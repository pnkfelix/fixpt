;; A file whose procedural macro's transformer passes `rename` to a helper,
;; which renames a value the file hides (`TODO.md` §300): reached through
;; its frame, which holds every value it hides.
(begin-for-syntax
  (define via-helper (subr pure ((subr pure (symbol) symbol)) symbol)
    (lambda (r) (r 'secret))))
(hide (define secret int 5))
(define-syntax get-secret (macro (_) expr)
  (er-macro-transformer (lambda (form rename compare) (via-helper rename))))
