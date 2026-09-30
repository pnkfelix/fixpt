; Facts through `or`, `and` and `not` (PLAN.md Q11): the else of an `or`
; knows what both its tests show when false, the then of an `and` what both
; show when true, and `not` swaps them. Conjunctions only; see
; `or-then-refused.fx`.
(define* f (subr pure (nat (listof int acyclic)) nat)
  (lambda (n xs) (if (or (= n 0) (null? xs)) 0 (- n 1))))
(define* g (subr pure (nat nat) nat)
  (lambda (a b) (if (and (>= a b) (not (= b 0))) (- a b) 0)))
(define* h (subr pure (nat) nat)
  (lambda (n) (if (not (= n 0)) (- n 1) 0)))
(list (f 3 nil) (g 5 2) (h 4))
