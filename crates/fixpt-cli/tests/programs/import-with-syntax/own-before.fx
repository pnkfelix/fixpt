;; A macro used before its file defines it.
(define two int (one 1))
(define-syntax one (expr) (syntax-rules () ((_ e) (+ e 1))))
