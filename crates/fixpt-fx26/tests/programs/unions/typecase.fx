; Accepted: `typecase`, the shape predicates as arms, each binding its member,
; and what each arm leaves narrowing the variable for those after it: here
; `(car x)` in the `else`, `x` no longer an `int`, a procedure or `nil`.
(define-type v (union int (listof int @r) (subr pure (int) int)))
(define* f (subr (read @r) (v) int)
  (lambda (x)
    (typecase x
      (int n (+ n 1))
      (procedure g (g 5))
      (nil e -1)
      (else (car x)))))
(f 3)
