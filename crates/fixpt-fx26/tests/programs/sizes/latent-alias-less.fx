; Rejected: an alias of `=` at a type that proves nothing, `bool`, shows
; nothing of sizes: in its `else`, `n` is not known to be 1 or more.
(define same (subr pure (int int) bool) =)
(define count (subr (read (globals same)) (nat) int)
  (letrec ((count (subr (read (globals same)) (nat) int)
             (lambda (n) (if (same n 0) 0 (+ 1 (count (- n 1)))))))
    count))
