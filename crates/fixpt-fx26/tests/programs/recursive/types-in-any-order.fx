; Types are declared ahead, so they may name each other in any order
; (PLAN.md Q11, TODO.md §13): an abbreviation naming one defined after it,
; and two datatypes that refer to each other. Values still see only the
; definitions before them.
(define-type forests (listof forest acyclic))
(define-datatype tree (leaf int) (node forest))
(define-datatype forest (none) (some tree forest))
(the forests (list (some (leaf 1) (some (node (none)) (none)))))
