; Tags and labels written as keywords (`docs/fx26.md`, "Keywords"): the
; same labels as the names written bare, which are still taken, in types,
; products, `extract`, sums and `tagcase` arms alike.
(define-type result (sumof (#:sorted (listof int acyclic)) (failed string)))
(define p (productof (#:n int) (reply string)) (product (#:n 3) (reply "x")))
(define size (subr pure (result) int)
  (lambda (r) (tagcase r (#:sorted xs 1) (#:failed m 2))))
(+ (+ (extract p #:n) (extract p n)) (+ (size (sum #:sorted '())) (size (sum failed "no"))))
