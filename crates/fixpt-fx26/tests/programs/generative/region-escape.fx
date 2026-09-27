; Rejected: a generative type still mentions the region it was given.
(define-generative (stack (t type) (r region)) (listof t r))
(define f (subr pure () (stack int @q)) (lambda () (letregion l (the (stack int l) (up-stack (the (listof int l) (cons 1 nil)))))))
