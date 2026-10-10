;; ! `checker` here is the module's own item, this one, not the `checker` bound outside it
;; An item capturing its own name (`TODO.md` §72).
(define checker (module (define checker int 1)))
(define m (module (define checker (with checker checker))))
