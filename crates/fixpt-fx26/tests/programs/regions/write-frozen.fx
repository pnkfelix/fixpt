; Rejected: a frozen list cannot be written.
(let ((xs (letfreeze r (the (listof int r) (cons 1 nil)))))
  (set-car! xs 2))
