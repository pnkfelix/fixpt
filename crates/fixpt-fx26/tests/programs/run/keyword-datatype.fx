; A `define-datatype` variant's tag written as a keyword (`docs/fx26.md`,
; "Keywords"): the same label as its name bare, its constructor the
; procedure of that name, which returns the datatype's type.
(define-datatype shape (#:circle int) (rect int int))
(define area (subr pure (shape) int)
  (lambda (s) (tagcase s (#:circle (r) (* 3 (* r r))) (#:rect (w h) (* w h)))))
(define made (subr pure ((subr pure (int) shape) int) shape) (lambda (f n) (f n)))
(+ (area (made circle 2)) (area (rect 3 4)))
