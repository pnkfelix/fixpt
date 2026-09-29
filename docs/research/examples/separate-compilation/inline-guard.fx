;;; Inlining under a guard, in FX-26 today: `twice`'s register code has
;;; `step`'s body in it, behind a check that the global `step` still holds
;;; the word it was inlined from. See it with `fixpt compile` on this file.

;;; ---- counter.fx ----
(define step (subr pure (int) int) (lambda (n) (+ n 1)))

;;; ---- client.fx ----
(define* twice (subr pure (int) int) (lambda (n) (step (step n))))
(twice 0)                                 ; 2
