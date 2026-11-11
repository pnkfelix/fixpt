;; A file's macro, used in its file and where the file is imported alike.
(define-syntax one (expr) (syntax-rules () ((_ e) (+ e 1))))
(define two int (one 1))
