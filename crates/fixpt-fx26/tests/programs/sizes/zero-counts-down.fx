;;; `zero?` proves what `(= n 0)` does (its latent propositions): in its
;;; `else`, `n ≥ 1`, so `(- n 1)` is a natural, and the recursion ends.
(define count (subr pure (nat) int)
  (letrec ((count (subr pure (nat) int)
             (lambda (n) (if (zero? n) 0 (+ 1 (count (- n 1)))))))
    count))
(count 7)
