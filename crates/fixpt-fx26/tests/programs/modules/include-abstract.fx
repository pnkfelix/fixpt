;; => 6
;; An `include` of a module made where it is included, not bound to a name:
;; its abstract types are the including module's own (`TODO.md` §69), its
;; items' types naming them, in scope for the module's own items.
(define m (module (include (module (define-generative t int)
                                   (define z t (up-t 5))
                                   (define get (subr pure (t) int) (lambda (c) (down-t c)))))
                  (define one-more (subr pure (t) int) (lambda (c) (+ (get c) 1)))))
(with m (one-more z))
