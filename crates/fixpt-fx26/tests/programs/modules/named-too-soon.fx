;; ! `fs` uses `g`, defined after it
;; Even naming a later procedure in a value is refused: it is not made yet
;; (`DONE.md` §37), so the conservative rule refuses `(if #f (g) 0)` too.
(define m (module
  (define fs int (if #f (g) 0))
  (define g (subr pure () int) (lambda () 1))))
1
