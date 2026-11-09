;; A file's macro may name only what its module shows: `hidden` is hidden.
(define secret int 7)
(hide (define hidden int 7))
(define-syntax peek (expr) (syntax-rules () ((_ e) (+ e hidden))))
