;; => 6
;; A macro that makes a definition (`(macro σ defn)`): the name its use gives
;; defined under that name, as the program sees it.
(define-syntax define-const
  (macro (_ bvar expr) defn)
  (syntax-rules
    ((_ n e) (define n e))))
(define-const x 5)
(+ x 1)
