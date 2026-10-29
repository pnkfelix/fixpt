;; => 0
;; A list joined with `nil` in an `if` (Heist's report, 2026-10-28): a pair
;; that may be `nil`, whose tail is a list of the same, is that list. It was
;; at a region of its own, refused as no `acyclic` list; now that a list
;; nothing places is `acyclic` (Heist's request, 2026-10-29, `TODO.md`
;; §174), it is one.
(define* f (subr pure ((listof int acyclic)) int) (lambda (l) 0))
(define* g (subr pure (int) int) (lambda (n) (let ((l (if (> n 0) (list n) nil))) (f l))))
0
