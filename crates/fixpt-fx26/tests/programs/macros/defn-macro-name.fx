;; ! `define-const` is a macro's name, which is not bound
(define-syntax define-const
  (-> (bvar expr) defn)
  (syntax-rules ()
    ((_ n e) (define n e))))
(define-const define-const 2)
