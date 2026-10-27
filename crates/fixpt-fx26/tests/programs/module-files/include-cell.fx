;; A file of parameters giving a type and a value of it, for the files that
;; include it made (`include-in-file*.fx`).
(module-parameters ((ed region)))
(define-type cell (ref int ed))
(define mk (subr (alloc ed) () cell) (lambda () (new 0)))
