;; A file that hides a value of a standard binding's name, `abs`, which its
;; macro names (`TODO.md` §300): the file's, not the standard one.
(hide (define abs (lambda ((n int)) 99)))
(define-syntax my-abs (macro (_ e @ expr) expr) (syntax-rules ((_ e) (abs e))))
