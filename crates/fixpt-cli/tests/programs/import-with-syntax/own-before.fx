;; A macro used before its file defines it.
(define two int (one 1))
(define-syntax one (macro (_ expr) expr) (syntax-rules ((_ e) (+ e 1))))
