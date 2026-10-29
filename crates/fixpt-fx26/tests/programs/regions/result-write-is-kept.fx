; Rejected (Heist's, 2026-10-29): a procedure polymorphic in `r` that writes
; what it allocated in `r` and returns says so. Masking keeps `read` and
; `write` on a region its result's type mentions, as Lucassen and Gifford's
; rule does, so `f`, declaring only `(alloc r)`, is refused here; were it
; not, `f` instantiated at `acyclic` would give `len` a cycle to walk for
; ever, `len` being `pure` and terminating.
(define f (poly ((r region)) (subr (alloc r) (int) (listof int r)))
  (plambda ((r region))
    (lambda (x) (let ((l (the (listof int r) (cons x nil)))) (begin (set-cdr! l l) l)))))
(define len (subr pure ((listof int acyclic)) int)
  (lambda (xs)
    (letrec ((go (subr pure ((listof int acyclic) int) int)
               (lambda (xs n) (if (null? xs) n (go (cdr xs) (+ n 1))))))
      (go xs 0))))
(len (the (listof int acyclic) (f 1)))
