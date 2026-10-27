;; => 5
;; In a `with` of a module a `let` binds to one written there, `f` is that
;; module's, not the item being made (Heist's problem B).
(define outer
  (module
    (define f (lambda () (let ((m (module (define f (subr pure () int) (lambda () 5)))))
                           (with m (f)))))))
((with outer f))
