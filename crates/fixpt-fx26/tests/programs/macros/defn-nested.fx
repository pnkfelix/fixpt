;; => 3
;; A macro that makes definitions by another's: each spliced, in order.
(define-syntax define-const
  (-> (bvar expr) defn)
  (syntax-rules ()
    ((_ n e) (define n e))))
(define-syntax define-two
  (-> (bvar bvar) defn)
  (syntax-rules ()
    ((_ a b) (begin (define-const a 1) (define-const b 2)))))
(define-two p q)
(+ p q)
