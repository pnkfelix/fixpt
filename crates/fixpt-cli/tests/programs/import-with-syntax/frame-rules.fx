;; A file whose `syntax-rules` macro names a value it hides (`TODO.md`
;; §300): reached through its frame.
(hide (define named int 41) (define unnamed int 2))
(define-syntax plus-named (macro (_ e @ expr) expr)
  (syntax-rules ((_ e) (+ e named))))
