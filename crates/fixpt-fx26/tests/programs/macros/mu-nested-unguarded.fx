;; ! a `mu`'s variable is used where no pair is around it
;; A `mu` whose variable is under another `mu` but no pair: `a` unfolds to
;; `(mu b a)`, which unfolds to `a`, never to syntax. Each `mu`'s body was
;; looked at alone, the inner one's variable not the outer's, and it was
;; let through.
(define-syntax bad
  (macro (_ . (mu a (mu b a))) expr)
  (syntax-rules ((_) 0)))
0
