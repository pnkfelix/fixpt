;; => 131
;; A `let`'s or a `lambda`'s binder shadows a macro of its name in its scope
;; (TODO.md §295): a list it heads there is an application; elsewhere a use.
(define-syntax foo (macro (_ expr) expr) (syntax-rules ((_ e) (+ e 100))))
(define double (lambda ((x int)) (* x 2)))
(+ (+ (foo 1) (let ((foo double)) (foo 10)))
   (+ (+ ((lambda ((foo (subr pure (int) int))) (foo 3)) double) (let ((foo 2)) foo))
      (+ (let ((foo double)) (if #t (foo 1) 0)) (- (let ((bar 1)) (foo bar)) 101))))
