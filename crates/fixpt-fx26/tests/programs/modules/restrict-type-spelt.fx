;; => 1
;; `restrict` keeps a type spelt as `import` spells it, `(type t)`, as by its plain name
;; (Heist's should-work note, entry 20).
(define m (module (define-type t int) (define x int 1)))
(define-type r (restrict (moduleof (desc t int) (val x int)) x (type t)))
(define n r m)
(with n x)
