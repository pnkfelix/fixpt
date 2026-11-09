;; ! `clamp` is a macro here, and `m` gives a value of that name
;; A `with` binds the names its module gives, which the expander cannot
;; see: a macro used in its body by a name the module gives a value of is
;; refused, rather than the program seeming to call that value.
(define m (module (define clamp (lambda ((x int)) (* x 2)))))
(define-syntax clamp (expr) (syntax-rules () ((_ e) (let ((v e)) (if (> v 10) 10 v)))))
(with m (clamp 100))
