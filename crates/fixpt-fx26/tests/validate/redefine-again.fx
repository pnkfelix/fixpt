;; `f` redefined at a type `g`'s call of it cannot take: `g`, checked
;; again, breaks; read again first (`k-rerun`, `read-again`), so that what
;; that check finds is of keys of its own, not `g`'s first ones.
(define f (subr pure (string) int) (lambda (s) (string-length s)))
(g 1)
(f "abc")
