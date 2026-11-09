;; ! a macro that makes definitions has no typed parts, not yet
(define-syntax define-int
  (-> (bvar (expr #:type int)) defn)
  (syntax-rules ()
    ((_ n e) (define n e))))
