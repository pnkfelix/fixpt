;; ! `clamp` is a macro's name, which is not defined again
;; So does an `import`.
(define m (module (define clamp 0)))
(define-syntax clamp (expr) (syntax-rules () ((_ e) (let ((v e)) (if (> v 10) 10 v)))))
(import m clamp)
(clamp 100)
