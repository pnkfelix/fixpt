;; ! must be told apart at run time: a (ref int @r) and a (ref bool @r) cannot be
;; Two cells: reading through either is sound, writing is not (a union of
;; cells is no cell of a union); refused until a program needs it
;; (logical-types.md §9.2, question 14).
(define f (subr pure ((anyof (ref int @r) (ref bool @r))) int) (lambda (c) 0))
