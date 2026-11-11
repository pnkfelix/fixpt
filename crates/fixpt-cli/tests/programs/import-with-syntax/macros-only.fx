;; A file of macros alone (Heist's): its module gives nothing else.
(define-syntax twice (syntax-rules () ((_ e) (let ((x e)) (+ x x)))))
