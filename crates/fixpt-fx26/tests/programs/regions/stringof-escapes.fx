; Rejected: a string made at a region that ends may not outlive it, as a
; bytevector may not.
(define leak (subr (alloc @heap) () int)
  (lambda ()
    (string-length (letregion r (the (stringof r) (make-string 3 #\a))))))
