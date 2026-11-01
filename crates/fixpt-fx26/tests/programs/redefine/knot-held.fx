;;; Landin's knot through a global that holds a procedure, not being one:
;;; `f` reads `tbl` and calls what it holds, and `tbl` is defined again to
;;; hold `f`. Every effect is true; the knot is tied by the write. Refused
;;; at `tbl`'s first definition, whose type permits it: a procedure kept in
;;; `tbl` that may read `tbl` (here, `@globals`) must say `spin`
;;; (`Checker::no_reaching_itself`).
(define-type box (productof (p (subr (read @globals) () int))))
(define tbl box (product (p (lambda () 0))))
(define f (subr (read @globals) () int) (lambda () ((extract tbl p))))
(define tbl box (product (p f)))
