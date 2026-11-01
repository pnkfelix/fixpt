;;; A knot through an I-cell at a `letfreeze`'s own region: a pair whose
;;; car is a cell, filled with the pair itself. `init` counts as a write,
;;; so the value leaves at `const`, not `acyclic`. Declaring `x` at
;;; `acyclic` instead is refused (`acyclic-shallow-and-deep.md` §2.2).
(define x (mu n (pairof (icell n const) int const))
  (letfreeze r
    (let ((c (the (icell (mu n (pairof (icell n r) int r)) r) (make-icell))))
      (let ((p (the (mu n (pairof (icell n r) int r)) (cons c 1))))
        (begin (icell-put! c p) p)))))
(eq? x (icell-get (car x)))
