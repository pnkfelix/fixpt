;; ! `extend` extends a module by a module, and its second is a int
;; Both of an `extend`'s are modules.
(define a (module (define x int 1)))
(extend a 2)
