;; => 11
;; A value: `#%toplevel:x` is `(with #%toplevel x)`.
(define x 10)
(let ((x 1)) (+ #%toplevel:x x))
