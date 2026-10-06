;; => 13
;; `define-datatype` in a module, expanded as a program's is: its type a
;; description, its constructors values; outside, `(select m shape)` is the
;; sum, taken apart by `tagcase` (`TODO.md` §34).
(define geometry (module
  (define-datatype shape (circle int) (rect int int))
  (define area (subr pure (shape) int)
    (lambda (s) (tagcase s (circle (r) (* 3 (* r r))) (rect (w h) (* w h)))))))
(define-type shape (select geometry shape))
(define rect (with geometry rect))
(define area (with geometry area))
(define big (subr pure (shape) bool)
  (lambda (s) (tagcase s (circle (r) (> r 10)) (rect (w h) (> (* w h) 100)))))
(+ (area (rect 3 4)) (if (big ((with geometry circle) 20)) 1 0))
