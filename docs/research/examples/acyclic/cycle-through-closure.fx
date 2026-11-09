;;; A cycle with no recursive type: the list holds procedures, and the ref
;;; holds such a list. A procedure that captures the ref (a local, not a
;;; global) closes c -> l -> f -> c through its environment, which its
;;; type does not show. The only trace is Landin's-knot rule, which makes
;;; the procedure's type say `spin` (`acyclic-shallow-and-deep.md` §1).
(define-type thunk (subr (maxeff (read @r) spin) () int))
(define-type thunks (listof thunk acyclic))
(define* knot (subr (maxeff (alloc @r) (write @r) (read @r) spin) () int)
  (lambda ()
    (let ((c (the (ref thunks @r) (new (the thunks (list))))))
      (let ((f (the thunk (lambda () (length (get c))))))
        (let ((l (the thunks (list f))))
          (begin (set c l)
                 ;; From c, through the list to f, which reads c again.
                 ((car (get c)))))))))
(knot)
