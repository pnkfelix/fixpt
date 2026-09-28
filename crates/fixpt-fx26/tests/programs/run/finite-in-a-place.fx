; Finite data in an arena: built there and frozen into it, walked by a
; procedure polymorphic in the place, which ends (no `spin`), and freed
; with the arena. The place is found from the argument's type.
(define len (poly ((p place)) (subr (read (finite p)) ((listof int (finite p)) int) int))
  (plambda ((p place))
    (letrec ((go (subr (read (finite p)) ((listof int (finite p)) int) int)
               (lambda (xs n) (if (null? xs) n (go (cdr xs) (+ n 1))))))
      go)))
(letrena a (len (letfreeze (r a) (the (listof int r) (rcons a 1 (rcons a 2 (rcons a 3 nil))))) 0))
