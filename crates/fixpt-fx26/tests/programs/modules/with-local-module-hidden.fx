;; ! `f` uses `f`, before it is made
;; A value the local module hides is not its to give: `f` is the item.
(define outer
  (module
    (define f (lambda () (let ((m (module (hide (define f int 1)) (define g int 2))))
                           (with m (f)))))))
