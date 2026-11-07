;; A file's macro is used where the file is imported, not in it, for now.
(define-syntax one (expr) ((_ e) (+ e 1)))
(define two int (one 1))
