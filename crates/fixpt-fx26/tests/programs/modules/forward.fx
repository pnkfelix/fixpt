;; => 52
;; A module's definitions see each other, as a `letrec*`'s (`DONE.md` §37):
;; a typed lambda may name an item after it, procedure or not, since it
;; does not run when it is made; procedures calling each other need no
;; `define-rec`. `y` runs `f` when it is made, after `limit`, which `f`
;; names; `g` names `h`, after it, and nothing runs `g` until the module is.
(define m (module
  (define f (subr pure (int) int) (lambda (a) (+ a limit)))
  (define limit int 10)
  (define y int (f 1))
  (define g (subr pure () int) (lambda () (h)))
  (define h (subr pure () int) (lambda () (+ y 30)))))
(with m (+ y (g)))
