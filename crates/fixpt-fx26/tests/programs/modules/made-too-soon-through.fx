;; ! `y` uses `get-x`, which uses `x`, defined after `y`
;; What a value's making may run is followed through the lambdas it names:
;; `y` runs `get-x`, which reads `x`, not made yet (`DONE.md` §37).
(define m (module
  (define get-x (subr pure () int) (lambda () x))
  (define y int (get-x))
  (define x int 1)))
1
