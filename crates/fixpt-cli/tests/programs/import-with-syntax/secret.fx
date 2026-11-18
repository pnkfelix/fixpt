;; A file's macro may name only what the file defines, or a standard name:
;; `nowhere` is neither.
(define secret int 7)
(hide (define hidden int 7))
(define-syntax peek (macro (_ expr) expr) (syntax-rules ((_ e) (+ e nowhere))))
