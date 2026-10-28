; Accepted: a walk of a list frozen into a place whose tail is the heap's
; frozen data ends: no cycle runs through it, and each tail is smaller, so
; no `spin` (Kayak's, 2026-10-28).
(define heap-list (listof int acyclic) (list 1 2 3))
(define* walk (poly ((p place)) (subr (read (acyclic p)) ((listof int (acyclic p))) int))
  (plambda ((p place))
    (lambda (xs)
      (letrec ((go (subr (read (acyclic p)) ((listof int (acyclic p)) int) int)
                 (lambda (ys n) (if (null? ys) n (go (cdr ys) (+ n 1))))))
        (go xs 0)))))
(letrena p ((proj walk p) (the (listof int (acyclic p)) (rcons p 0 (rcons p 0 heap-list)))))
