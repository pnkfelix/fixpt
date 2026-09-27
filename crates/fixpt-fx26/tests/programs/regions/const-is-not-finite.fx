; Rejected: data a `letfreeze` wrote may be cyclic (here it is), so it is
; `const`, not `finite`. The write is noted though masking hides it from
; the body's effect.
(define len (subr spin ((listof int finite) int) int)
  (lambda (xs n) (if (null? xs) n (len (cdr xs) (+ n 1)))))
(len (letfreeze r (let ((ys (the (listof int r) (cons 1 nil)))) (begin (set-cdr! ys ys) ys))) 0)
