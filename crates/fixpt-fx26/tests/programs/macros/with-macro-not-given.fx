;; => 21
;; A macro used in a `with` whose module gives no value of its name is the
;; macro; one the module does give is the module's, used by a name no macro
;; has; and a template's use of a macro is that macro, whatever the `with`
;; around the use gives.
(define m (module (define double (lambda ((x int)) (* x 2))) (define clamp 0)))
(define n (module (define double (lambda ((x int)) (* x 2)))))
(define-syntax clamp (expr) (syntax-rules () ((_ e) (let ((v e)) (if (> v 10) 10 v)))))
(define-syntax clamped (expr) (syntax-rules () ((_ e) (clamp e))))
(+ (with n (double (clamp 100))) (- (with m (clamped 1)) (with m clamp)))
