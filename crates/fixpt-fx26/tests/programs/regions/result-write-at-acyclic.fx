; Rejected (Heist's, 2026-10-29): the same procedure, saying that it writes
; its result's region (`result-write-is-kept.fx`), is refused where it is
; instantiated at `acyclic`: that writes frozen data.
(define f (poly ((r region)) (subr (maxeff (alloc r) (write r)) (int) (listof int r)))
  (plambda ((r region))
    (lambda (x) (let ((l (the (listof int r) (cons x nil)))) (begin (set-cdr! l l) l)))))
(define len (subr pure ((listof int acyclic)) int)
  (lambda (xs)
    (letrec ((go (subr pure ((listof int acyclic) int) int)
               (lambda (xs n) (if (null? xs) n (go (cdr xs) (+ n 1))))))
      (go xs 0))))
(len (the (listof int acyclic) (f 1)))
