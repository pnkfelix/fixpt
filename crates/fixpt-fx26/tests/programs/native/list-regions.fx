;;; `list` at any region, as a `cons` chain may be: a list it makes at `@heap`
;;; can be written. As a value it copies, so `apply` of it cannot give an
;;; `acyclic` list (given as it is, F11) at a region that can be written.
;;; (Not in `run/`: the evaluator loses a `set-car!` on a global, TODO §18.)
(define h (listof int @heap) (list 1 2 3))
(set-car! h 10)
(define a (listof int acyclic) (list 4 5))
(define hs (listof int @heap) (apply list a))
(set-car! hs 40)
(+ (car h) (+ (car a) (car hs)))
