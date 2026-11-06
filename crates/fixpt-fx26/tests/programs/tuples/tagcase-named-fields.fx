;; ! only a product labelled 1, 2, …, a `tupleof`, is taken apart by position
;; A product with names of its own is not taken apart by position
;; (`TODO.md` §191): `x` and `y` would not be `w` and `h`.
(tagcase (sum #:rect (product (#:w 1) (#:h 2))) (#:rect (x y) x))
