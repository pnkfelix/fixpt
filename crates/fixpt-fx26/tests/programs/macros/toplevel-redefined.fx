;; => 13
;; The top level's name as it is where the macro is used: redefined, the
;; new value, as a plain use of the global sees it.
(define limit int 10)
(define-syntax clamp (expr) (syntax-rules () ((_ e) (let ((v e)) (if (> v limit) limit v)))))
(define f (subr (read (globals limit)) (int) int) (lambda (limit) (clamp (+ limit 5))))
(define limit int 13)
(f 20)
