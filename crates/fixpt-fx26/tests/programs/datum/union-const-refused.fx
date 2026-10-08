;;; A datum's pairs are `acyclic`: frozen data that may have a cycle is not
;;; a datum until `acyclic` finds it has none.
(define ring (subr pure () (listof int const))
  (lambda ()
    (letfreeze r
      (let ((ys (the (listof int r) (list 1 2))))
        (begin (set-cdr! (cdr ys) ys) ys)))))
(define d datum (ring))
