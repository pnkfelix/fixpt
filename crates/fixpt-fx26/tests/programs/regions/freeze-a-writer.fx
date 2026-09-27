; Rejected: what leaves a `letfreeze` may not keep a way to write its data.
(letfreeze r
  (let ((xs (the (listof int r) (cons 1 nil))))
    (lambda () (set-car! xs 2))))
