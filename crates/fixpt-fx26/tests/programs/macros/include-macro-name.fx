;; ! `clamp` is a macro's name, which is not defined again
;; A top-level `include` defines what its module gives, after expansion:
;; a name of a macro defined before is refused, as a `define` of it is.
(define m (module (define clamp 0)))
(define-syntax clamp (expr) (syntax-rules () ((_ e) (let ((v e)) (if (> v 10) 10 v)))))
(include m)
(clamp 100)
