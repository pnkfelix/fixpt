;; => 3
;; A `poly` in an equi-recursive type: a command takes a list of commands,
;; each polymorphic in its own region. Instantiated, a command's own binder
;; is its instance's, and the commands in the list stay polymorphic: the
;; substitution stops at their `poly`, which binds the same variable
;; (Heist's, `TODO.md` §211, 4). It once went in, the list's commands
;; reading the instance's region, so a knot was found where there is none.
;; And a global of a `poly` type given where one is wanted: compared, not
;; held to be pure (§211, 5).
(define-type cmd
  (poly ((r region)) (subr (maxeff spin (read r)) ((ref (listof cmd acyclic) r)) int)))
(define leaf cmd (plambda ((r region)) (lambda (c) 1)))
(define count cmd (plambda ((r region)) (lambda (c) (length (get c)))))
(define run (subr (maxeff spin (read @heap) (alloc @heap) (read (globals leaf count))) () int)
  (lambda ()
    (let ((cs (the (ref (listof cmd acyclic) @heap) (new (list leaf count)))))
      (letregion q
        (let ((mine (the (ref (listof cmd acyclic) q) (new (list count count count)))))
          ((proj (car (cdr (get cs))) q) mine))))))
(run)
