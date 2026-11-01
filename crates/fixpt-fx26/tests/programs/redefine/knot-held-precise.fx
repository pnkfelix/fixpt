;;; The same knot, every effect precise: a type whose procedure reads the
;;; global the type is of permits it, so its first definition is refused,
;;; whatever the value, as a ref's type is that keeps such a procedure.
(define-type box (productof (p (subr (read (globals tbl)) () int))))
(define tbl box (product (p (lambda () 0))))
