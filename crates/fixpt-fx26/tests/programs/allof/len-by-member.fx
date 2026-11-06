;; => (3 2)
;; Termination judged member by member (`logical-types.md` §8.5): on an
;; `acyclic` list `len` ends, so a call at that member says no `spin`; on
;; a list at `@heap`, which may be cyclic, it may not, and says `spin`.
(define-type heap-ints (listof int @heap))
(define len (allof (subr pure ((listof int acyclic)) int)
                   (subr (maxeff (read @heap) spin) (heap-ints) int))
  (letrec ((len (allof (subr pure ((listof int acyclic)) int)
                       (subr (maxeff (read @heap) spin) (heap-ints) int))
             (lambda (l) (if (null? l) 0 (+ 1 (len (cdr l)))))))
    len))
(define xs heap-ints (list 1 2))
(list (len (list 1 2 3)) (len xs))
