;; ! `hi` is a trailmark, which is not bound
;; A trailmark is no binder: a use may not bind its name.
(define-syntax hi (trailmark))
(define-syntax let1 (syntax-rules ((_ x e body) (let ((x e)) body))))
(let1 hi 1 2)
