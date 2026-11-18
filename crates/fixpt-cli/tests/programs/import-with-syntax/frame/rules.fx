(hide (define named int 41) (define unnamed int 2))
(define shown int 1)
(define-syntax plus-named (macro (_ e @ expr) expr)
  (syntax-rules ((_ e) (+ e named))))
