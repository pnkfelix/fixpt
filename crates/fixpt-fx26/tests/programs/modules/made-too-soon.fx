;; ! `y` uses `x`, defined after it
;; A value is made when its item is: it may use only items made before it
;; (`DONE.md` §37). Refused before it runs, not left to fail.
(define m (module
  (define y int (+ x 1))
  (define x int 1)))
1
