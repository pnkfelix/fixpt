;; => 0
;; A list type imported with a family whose body names it (Heist's report,
;; 2026-10-28): both checkers print the import's `cmds` as `(listof …)`.
;; The FX-26 checker, sharing equal nodes, showed it by a node other than
;; its class's first (the copy in `msg`'s body), and so unfolded it once.
(define m
  (module
    (define-type cmd (subr pure () unit))
    (define-type cmds (listof cmd acyclic))
    (define-type (reply (s type)) (productof (state s) (cmds cmds)))
    (define-type (msg (s type)) (subr pure (s) (reply s)))))
(define n (module (import m (type msg cmds))))
0
