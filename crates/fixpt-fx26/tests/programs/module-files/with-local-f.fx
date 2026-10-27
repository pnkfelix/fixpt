;; A module file whose item opens a module it makes, for `with-local-module.fx`.
(define f (lambda () (let ((m (module (define f (subr pure () int) (lambda () 5))))) (with m (f)))))
