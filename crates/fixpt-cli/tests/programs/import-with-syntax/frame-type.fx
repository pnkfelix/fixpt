;; A file whose macro's template names a type it hides (`TODO.md` §300):
;; reached through its frame, by its alias there, `%ft:secret-t`.
(hide (define-type secret-t (productof (n int))))
(define-syntax mk (macro (_ e @ expr) expr) (syntax-rules ((_ e) (the secret-t e))))
