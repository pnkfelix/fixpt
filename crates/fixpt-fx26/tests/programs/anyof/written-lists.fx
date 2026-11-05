;; ! may be written must be told apart at run time: a (listof int @r) and a (listof bool @r)
;; Two lists that may be written: a pair of either could be given a part of
;; the other's type. Refused, as cells are; two `acyclic` lists are not.
(define f (subr pure ((anyof (listof int @r) (listof bool @r))) int) (lambda (l) 0))
