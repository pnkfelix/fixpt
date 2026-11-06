;; ! it may not end
;; A member may not say `pure` where its own calls may not end: a list at
;; `@heap` may be cyclic, so `(cdr l)` is no smaller.
(define-type heap-ints (listof int @heap))
(define len (allof (subr pure ((listof int acyclic)) int)
                   (subr (read @heap) (heap-ints) int))
  (letrec ((len (allof (subr pure ((listof int acyclic)) int)
                       (subr (read @heap) (heap-ints) int))
             (lambda (l) (if (null? l) 0 (+ 1 (len (cdr l)))))))
    len))
(len (list 1 2 3))
