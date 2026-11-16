;; ! is placed where it may be placed more than once
;; One placement that hides a duplication: `e` given to `both`, whose
;; signature says it places it any number of times, without saying so of
;; its own.
(define-syntax both
  (macro (_ (many expr)) expr)
  (syntax-rules
    ((_ e) (list e e))))
(define-syntax once-they-say
  (macro (_ expr) expr)
  (syntax-rules
    ((_ e) (both e))))
