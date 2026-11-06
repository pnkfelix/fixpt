;; ! only a product labelled 1, 2, …, a `tupleof`, is taken apart by position
;; Labels 2 then 1 are not in order: bind it to one name and `extract`.
(tagcase (sum #:p (product (2 1) (1 "x"))) (#:p (x y) y))
