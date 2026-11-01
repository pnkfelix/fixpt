;;; A global may hold a procedure that reads it if it says `spin`: then
;;; nothing claims the knot ends.
(define-type box (productof (p (subr (maxeff spin (read @globals)) () int))))
(define tbl box (product (p (lambda () 0))))
(define f (subr (maxeff spin (read @globals)) () int) (lambda () ((extract tbl p))))
(define tbl box (product (p f)))
