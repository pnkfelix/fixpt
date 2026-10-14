;; ! a `race` branch may be stopped half way, so it must do nothing another could see
;; Refused: a branch that writes what is outside it, which a branch
;; stopped half way and one run to its end would leave differently.
(define x (ref int @x) (new 0))
(race (begin (set x 1) 1) 2)
